/*-------------------------------------------------------------------------
 *
 * ginpostinglist.c
 *	  routines for dealing with posting lists.
 *
 *
 * Portions Copyright (c) 1996-2017, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *			src/backend/access/gin/ginpostinglist.c
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "access/gin_private.h"

#ifdef USE_ASSERT_CHECKING
#define CHECK_ENCODING_ROUNDTRIP
#endif

/*
 * For encoding purposes, item pointers are represented as 64-bit unsigned
 * integers. The lowest 11 bits represent the offset number, and the next
 * lowest 32 bits are the block number. That leaves 17 bits unused, i.e.
 * only 43 low bits are used.
 *
 * These 43-bit integers are encoded using varbyte encoding. In each byte,
 * the 7 low bits contain data, while the highest bit is a continuation bit.
 * When the continuation bit is set, the next byte is part of the same
 * integer, otherwise this is the last byte of this integer.  43 bits fit
 * conveniently in at most 6 bytes when varbyte encoded (the 6th byte does
 * not need a continuation bit, because we know the max size to be 43 bits):
 *
 * 0XXXXXXX
 * 1XXXXXXX 0XXXXYYY
 * 1XXXXXXX 1XXXXYYY 0YYYYYYY
 * 1XXXXXXX 1XXXXYYY 1YYYYYYY 0YYYYYYY
 * 1XXXXXXX 1XXXXYYY 1YYYYYYY 1YYYYYYY 0YYYYYYY
 * 1XXXXXXX 1XXXXYYY 1YYYYYYY 1YYYYYYY 1YYYYYYY YYYYYYYY
 *
 * X = bits used for offset number
 * Y = bits used for block number
 *
 * The bytes are in stored in little-endian order.
 *
 * An important property of this encoding is that removing an item from list
 * never increases the size of the resulting compressed posting list. Proof:
 *
 * Removing number is actually replacement of two numbers with their sum. We
 * have to prove that varbyte encoding of a sum can't be longer than varbyte
 * encoding of its summands. Sum of two numbers is at most one bit wider than
 * the larger of the summands. Widening a number by one bit enlarges its length
 * in varbyte encoding by at most one byte. Therefore, varbyte encoding of sum
 * is at most one byte longer than varbyte encoding of larger summand. Lesser
 * summand is at least one byte, so the sum cannot take more space than the
 * summands, Q.E.D.
 *
 * This property greatly simplifies VACUUM, which can assume that posting
 * lists always fit on the same page after vacuuming. Note that even though
 * that holds for removing items from a posting list, you must also be
 * careful to not cause expansion e.g. when merging uncompressed items on the
 * page into the compressed lists, when vacuuming.
 */

/*
 * How many bits do you need to encode offset number? OffsetNumber is a 16-bit
 * integer, but you can't fit that many items on a page. 11 ought to be more
 * than enough. It's tempting to derive this from MaxHeapTuplesPerPage, and
 * use the minimum number of bits, but that would require changing the on-disk
 * format if MaxHeapTuplesPerPage changes. Better to leave some slack.
 */
#define MaxHeapTuplesPerPageBits		11

static inline uint64
itemptr_to_uint64(const ItemPointer iptr)
{
	uint64		val;

	Assert(ItemPointerIsValid(iptr));
	Assert(GinItemPointerGetOffsetNumber(iptr) < (1 << MaxHeapTuplesPerPageBits));

	val = GinItemPointerGetBlockNumber(iptr);
	val <<= MaxHeapTuplesPerPageBits;
	val |= GinItemPointerGetOffsetNumber(iptr);

	return val;
}

static inline void
uint64_to_itemptr(uint64 val, ItemPointer iptr)
{
	GinItemPointerSetOffsetNumber(iptr, val & ((1 << MaxHeapTuplesPerPageBits) - 1));
	val = val >> MaxHeapTuplesPerPageBits;
	GinItemPointerSetBlockNumber(iptr, val);

	Assert(ItemPointerIsValid(iptr));
}

/*
 * Varbyte-encode 'val' into *ptr. *ptr is incremented to next integer.
 */
static void
encode_varbyte(uint64 val, unsigned char **ptr)
{
	unsigned char *p = *ptr;

	while (val > 0x7F)
	{
		*(p++) = 0x80 | (val & 0x7F);
		val >>= 7;
	}
	*(p++) = (unsigned char) val;

	*ptr = p;
}

/*
 * Decode varbyte-encoded integer at *ptr. *ptr is incremented to next integer.
 */
static uint64
decode_varbyte(unsigned char **ptr)
{
	uint64		val;
	unsigned char *p = *ptr;
	uint64		c;

	c = *(p++);
	val = c & 0x7F;
	if (c & 0x80)
	{
		c = *(p++);
		val |= (c & 0x7F) << 7;
		if (c & 0x80)
		{
			c = *(p++);
			val |= (c & 0x7F) << 14;
			if (c & 0x80)
			{
				c = *(p++);
				val |= (c & 0x7F) << 21;
				if (c & 0x80)
				{
					c = *(p++);
					val |= (c & 0x7F) << 28;
					if (c & 0x80)
					{
						c = *(p++);
						val |= (c & 0x7F) << 35;
						if (c & 0x80)
						{
							/* last byte, no continuation bit */
							c = *(p++);
							val |= c << 42;
						}
					}
				}
			}
		}
	}

	*ptr = p;

	return val;
}

/*
 * Encode a posting list.
 *
 * The encoded list is returned in a palloc'd struct, which will be at most
 * 'maxsize' bytes in size.  The number items in the returned segment is
 * returned in *nwritten. If it's not equal to nipd, not all the items fit
 * in 'maxsize', and only the first *nwritten were encoded.
 *
 * The allocated size of the returned struct is short-aligned, and the padding
 * byte at the end, if any, is zero.
 */
GinPostingList *
ginCompressPostingList(const ItemPointer ipd, int nipd, int maxsize,
					   int *nwritten)
{
	uint64		prev;
	int			totalpacked = 0;
	int			maxbytes;
	GinPostingList *result;
	unsigned char *ptr;
	unsigned char *endptr;

	maxsize = SHORTALIGN_DOWN(maxsize);

	result = palloc(maxsize);

	maxbytes = maxsize - offsetof(GinPostingList, bytes) - SizeOfGinPostingListHeader;
	Assert(maxbytes > 0);

	/* Store the first special item */
	result->first = ipd[0];

	prev = itemptr_to_uint64(&result->first);

	ptr = result->bytes + SizeOfGinPostingListHeader;
	endptr = ptr + maxbytes;
	for (totalpacked = 1; totalpacked < nipd; totalpacked++)
	{
		uint64		val = itemptr_to_uint64(&ipd[totalpacked]);
		uint64		delta = val - prev;

		Assert(val > prev);

		if (endptr - ptr >= 6)
			encode_varbyte(delta, &ptr);
		else
		{
			/*
			 * There are less than 6 bytes left. Have to check if the next
			 * item fits in that space before writing it out.
			 */
			unsigned char buf[6];
			unsigned char *p = buf;

			encode_varbyte(delta, &p);
			if (p - buf > (endptr - ptr))
				break;			/* output is full */

			memcpy(ptr, buf, p - buf);
			ptr += (p - buf);
		}
		prev = val;
	}

	GinSetNumBytesInPostingList(result, ptr - result->bytes);
	GinSetNumItemsInPostingList(result, totalpacked);
	GinSetHasExtHeaderInPostingList(result);

	/*
	 * If we wrote an odd number of bytes, zero out the padding byte at the
	 * end.
	 */
	if (GinNumBytesInPostingList(result) != SHORTALIGN(GinNumBytesInPostingList(result)))
		result->bytes[GinNumBytesInPostingList(result)] = 0;

	if (nwritten)
		*nwritten = totalpacked;

	Assert(SizeOfGinPostingList(result) <= maxsize);

	/*
	 * Check that the encoded segment decodes back to the original items.
	 */
#if defined (CHECK_ENCODING_ROUNDTRIP)
	{
		int			ndecoded;
		ItemPointer	tmp = ginPostingListDecode(result, &ndecoded);
		int			i;

		Assert(ndecoded == totalpacked);
		for (i = 0; i < ndecoded; i++)
			Assert(memcmp(&tmp[i], &ipd[i], sizeof(ItemPointerData)) == 0);
		pfree(tmp);
	}
#endif

	return result;
}

void
internalGinDecodeSegment(GinPostingList *segment, ItemPointerData *to_list)
{
	int ndecoded;
	uint64 val;
	unsigned char *ptr;
	unsigned char *endptr;

	Assert(GinHasExtHeaderInPostingList(segment));

	to_list[0] = segment->first;
	ndecoded = 1;

	val = itemptr_to_uint64(&segment->first);
	ptr = segment->bytes + SizeOfGinPostingListHeader;
	endptr = segment->bytes + GinNumBytesInPostingList(segment);
	while (ptr < endptr)
	{
		val += decode_varbyte(&ptr);

		uint64_to_itemptr(val, &to_list[ndecoded]);
		ndecoded++;
	}

	Assert(ndecoded == GinNumItemsInPostingList(segment));
}

void
internalGinDecodeItem(GinPostingListDecoder *decoder, int index)
{
	GinPostingList *segment;
	Pointer endseg;
	int segmentStartInd = 0;
	int segmentEndInd = 0;

	Assert(decoder->page != NULL);
	Assert(decoder->segmentsByteLen > 0);

	segment = (GinPostingList *)(((Pointer)decoder->page) + decoder->segmentByteOffset);
	endseg = ((Pointer)segment) + decoder->segmentsByteLen;

	/* Find segment with matching item at index */
	while ((Pointer)segment < endseg)
	{
		Assert(GinHasExtHeaderInPostingList(segment));

		segmentEndInd += GinNumItemsInPostingList(segment);

		if (segmentEndInd > index)
		{
			break;
		}

		segmentStartInd = segmentEndInd;

		segment = GinNextPostingListSegment(segment);
	}

	Assert((Pointer)segment < endseg);
	Assert(OffsetNumberIsValid(ItemPointerGetOffsetNumber(&segment->first)));

	Assert(index >= segmentStartInd);
	Assert(index < segmentEndInd);

	internalGinDecodeSegment(segment, decoder->list + segmentStartInd);
	
	Assert(ItemPointerIsValid(&decoder->list[index]));
}

/*
* Read TIDs from leaf data page to single uncompressed array. The TIDs are
* returned in ascending order.
*
* advancePast is a hint, indicating that the caller is only interested in
* TIDs > advancePast. To return all items, use ItemPointerSetMin.
*
* Note: This function can still return items smaller than advancePast that
* are in the same posting list as the items of interest, so the caller must
* still check all the returned items. But passing it allows this function to
* skip whole posting lists.
*/
GinPostingListDecoder*
ginInitPostingListDecoder(Page page, ItemPointer advancePast, int *nitems_out)
{
	GinPostingListDecoder *result;
	GinPostingList	*next;
	GinPostingList	*segment;
	GinPostingList	*origsegment;
	Size			len;
	Size			offset = 0;
	Pointer			endseg;
	int				nitems = 0;
	bool			hasheader;

	if (GinPageIsCompressed(page))
	{
		segment = GinDataLeafPageGetPostingList(page);
		endseg = ((Pointer)segment) + GinDataLeafPageGetPostingListSize(page);

		/* Skip to the segment containing advancePast+1 */
		if (ItemPointerIsValid(advancePast))
		{
			next = GinNextPostingListSegment(segment);
			while ((Pointer)next < endseg &&
				ginCompareItemPointers(&next->first, advancePast) <= 0)
			{
				segment = next;
				next = GinNextPostingListSegment(segment);
			}
		}

		len = endseg - (Pointer)segment;
		offset = (Pointer)segment - (Pointer)page;

		if (len > 0)
		{
			hasheader = GinHasExtHeaderInPostingList(segment);

			if (hasheader)
			{
				origsegment = segment;

				/*
				* Calculate number of encoded items from segments.
				* We do the actual decoding later on-demand.
				*/
				while ((Pointer)segment < endseg)
				{
					if (!GinHasExtHeaderInPostingList(segment))
					{
						hasheader = false;
						break;
					}

					nitems += GinNumItemsInPostingList(segment);
					segment = GinNextPostingListSegment(segment);
				}

				segment = origsegment;
			}

			if (hasheader)
			{
				result = palloc0(offsetof(GinPostingListDecoder, list)
								+ sizeof(ItemPointerData) * nitems);

				result->numDecoded = 0;
			}
			else
			{
				uint64		  val;
				unsigned char *ptr;
				unsigned char *endptr;
				uint32		  nallocated;
				ItemPointer	  items;

				nitems = 0;

				/*
				* Guess an initial size of the array.
				*/
				nallocated = GinNumBytesInPostingList(segment) * 2 + 1;
				items = palloc(nallocated * sizeof(ItemPointerData));

				/*
				* We have to decode everything since we have no prior
				* knowledge about the number of encoded items.
				*/

				while ((Pointer)segment < endseg)
				{
					/* enlarge output array if needed */
					if (nitems >= nallocated)
					{
						nallocated *= 2;
						items = repalloc(items, nallocated * sizeof(ItemPointerData));
					}

					/* copy the first item */
					Assert(OffsetNumberIsValid(ItemPointerGetOffsetNumber(&segment->first)));
					Assert(nitems == 0 || ginCompareItemPointers(&segment->first, &items[nitems - 1]) > 0);
					items[nitems] = segment->first;
					nitems++;

					val = itemptr_to_uint64(&segment->first);
					ptr = segment->bytes;
					endptr = segment->bytes + GinNumBytesInPostingList(segment);
					while (ptr < endptr)
					{
						/* enlarge output array if needed */
						if (nitems >= nallocated)
						{
							nallocated *= 2;
							items = repalloc(items, nallocated * sizeof(ItemPointerData));
						}

						val += decode_varbyte(&ptr);

						uint64_to_itemptr(val, &items[nitems]);
						nitems++;
					}
					segment = GinNextPostingListSegment(segment);
				}

				result = palloc(offsetof(GinPostingListDecoder, list)
								+ sizeof(ItemPointerData) * nitems);

				memcpy(result->list, items, nitems * sizeof(ItemPointerData));
				result->numDecoded = nitems;

				pfree(items);
			}
		}
		else
		{
			result = palloc(offsetof(GinPostingListDecoder, list));
			result->numDecoded = 0;
		}

		result->page = page;
		result->segmentByteOffset = offset;
		result->segmentsByteLen = len;
		result->numItems = nitems;
	}
	else
	{
		Pointer ptr = GinDataPageGetData(page);

		/*
		* In the old pre-9.4 page format, the whole page content is used for
		* uncompressed items, and the number of items is stored in 'maxoff'
		*/
		nitems = GinPageGetOpaque(page)->maxoff;

		result = palloc(offsetof(GinPostingListDecoder, list)
						+ sizeof(ItemPointerData) * nitems);

		result->page = page;
		result->segmentByteOffset = ptr - (Pointer)page;
		result->segmentsByteLen = sizeof(ItemPointerData) * nitems;
		result->numItems = nitems;
		result->numDecoded = nitems;
		memcpy(result->list, (ItemPointer)ptr, result->segmentsByteLen);
	}

	if (nitems_out)
		*nitems_out = nitems;

	return result;
}

void
internalGinPostingListDecode(GinPostingList *plist, ItemPointer *to_list, uint32 nallocated, int *ndecoded_out)
{
	uint64			val;
	int				ndecoded;
	unsigned char	*ptr;
	unsigned char	*endptr;

	/* copy the first item */
	Assert(OffsetNumberIsValid(ItemPointerGetOffsetNumber(&plist->first)));
	(*to_list)[0] = plist->first;
	ndecoded = 1;

	val = itemptr_to_uint64(&plist->first);
	ptr = plist->bytes + (GinHasExtHeaderInPostingList(plist) ? SizeOfGinPostingListHeader : 0);
	endptr = plist->bytes + GinNumBytesInPostingList(plist);
	while (ptr < endptr)
	{
		/* enlarge output array if needed */
		if (ndecoded >= nallocated)
		{
			nallocated *= 2;
			*to_list = repalloc(*to_list, nallocated * sizeof(ItemPointerData));
		}

		val += decode_varbyte(&ptr);

		uint64_to_itemptr(val, &(*to_list)[ndecoded]);
		ndecoded++;
	}

	if (ndecoded_out)
		*ndecoded_out = ndecoded;
}

/*
* Read item pointers from leaf entry tuple.
*
* Returns a palloc'd array of ItemPointers. The number of items is returned
* in *nitems.
*/
GinPostingListDecoder*
ginInitPostingListDecoderFromTuple(Page page, IndexTuple itup, int *nitems_out)
{
	Pointer				  ptr = GinGetPosting(itup);
	int					  nitems = GinGetNPosting(itup);
	GinPostingListDecoder *result;

	result = palloc0(offsetof(GinPostingListDecoder, list)
					 + sizeof(ItemPointerData) * nitems);

	result->numItems = nitems;
	result->numDecoded = nitems;

	if (GinItupIsCompressed(itup))
	{
		GinPostingList *plist = (GinPostingList *)ptr;
		ItemPointer list = result->list;

		result->page = page;
		result->segmentByteOffset = ptr - (Pointer)page;
		result->segmentsByteLen = SizeOfGinPostingList(plist);

		internalGinPostingListDecode(plist, &list, nitems, NULL);
	}
	else
	{
		result->page = page;
		result->segmentByteOffset = ptr - (Pointer)page;
		result->segmentsByteLen = sizeof(ItemPointerData) * nitems;

		if (nitems > 0)
		{
			memcpy(result->list, ptr, result->segmentsByteLen);
		}
	}

	if (nitems_out)
		*nitems_out = nitems;

	return result;
}

/*
 * Add all item pointers from a bunch of posting lists to a TIDBitmap.
 */
int
ginPostingListDecodeAllSegmentsToTbm(Page page, TIDBitmap *tbm)
{
	GinPostingListDecoder	*decoder;
	GinPostingList			*segment;
	Pointer					endseg;
	int						segmentStartInd = 0;
	int						nitems;

	segment = (GinPostingList *)GinDataLeafPageGetPostingList(page);
	endseg = ((Pointer)segment) + GinDataLeafPageGetPostingListSize(page);

	decoder = ginInitPostingListDecoder(page, NULL, &nitems);

	if (decoder->numDecoded != nitems)
	{
		while ((Pointer)segment < endseg)
		{
			Assert(GinHasExtHeaderInPostingList(segment));

			internalGinDecodeSegment(segment, decoder->list + segmentStartInd);

			segmentStartInd += GinNumItemsInPostingList(segment);
			segment = GinNextPostingListSegment(segment);
		}
	}

	tbm_add_tuples(tbm, decoder->list, nitems, false);

	pfree(decoder);

	return nitems;
}

/*
* Decode a compressed posting list into an array of item pointers.
* The number of items is returned in *ndecoded.
*/
ItemPointer
ginPostingListDecode(GinPostingList *plist, int *ndecoded_out)
{
	ItemPointer		result;
	uint32			nallocated;

	if (GinHasExtHeaderInPostingList(plist))
	{
		/*
		* Get number of encoded items from plist
		*/
		nallocated = GinNumItemsInPostingList(plist);
	}
	else
	{
		/*
		* Guess an initial size of the array.
		*/
		nallocated = GinNumBytesInPostingList(plist) * 2 + 1;
	}

	result = palloc(nallocated * sizeof(ItemPointerData));

	internalGinPostingListDecode(plist, &result, nallocated, ndecoded_out);

	return result;
}

/*
 * Merge two ordered arrays of itempointers, eliminating any duplicates.
 *
 * Returns a palloc'd array, and *nmerged is set to the number of items in
 * the result, after eliminating duplicates.
 */
ItemPointer
ginMergeItemPointers(ItemPointerData *a, uint32 na,
					 ItemPointerData *b, uint32 nb,
					 int *nmerged)
{
	ItemPointerData *dst;

	dst = (ItemPointer) palloc((na + nb) * sizeof(ItemPointerData));

	/*
	 * If the argument arrays don't overlap, we can just append them to each
	 * other.
	 */
	if (na == 0 || nb == 0 || ginCompareItemPointers(&a[na - 1], &b[0]) < 0)
	{
		memcpy(dst, a, na * sizeof(ItemPointerData));
		memcpy(&dst[na], b, nb * sizeof(ItemPointerData));
		*nmerged = na + nb;
	}
	else if (ginCompareItemPointers(&b[nb - 1], &a[0]) < 0)
	{
		memcpy(dst, b, nb * sizeof(ItemPointerData));
		memcpy(&dst[nb], a, na * sizeof(ItemPointerData));
		*nmerged = na + nb;
	}
	else
	{
		ItemPointerData *dptr = dst;
		ItemPointerData *aptr = a;
		ItemPointerData *bptr = b;

		while (aptr - a < na && bptr - b < nb)
		{
			int			cmp = ginCompareItemPointers(aptr, bptr);

			if (cmp > 0)
				*dptr++ = *bptr++;
			else if (cmp == 0)
			{
				/* only keep one copy of the identical items */
				*dptr++ = *bptr++;
				aptr++;
			}
			else
				*dptr++ = *aptr++;
		}

		while (aptr - a < na)
			*dptr++ = *aptr++;

		while (bptr - b < nb)
			*dptr++ = *bptr++;

		*nmerged = dptr - dst;
	}

	return dst;
}
