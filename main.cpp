/*
The MIT License (MIT)

Copyright (c) 2014 berupon@gmail.com

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
*/

#include <stdio.h>
#include <stdint.h>
#include <math.h>
#include <errno.h>
#include <cassert>
#include <algorithm>

#include "timer.h"

/*

bitscan
https://chessprogramming.wikispaces.com/BitScan
http://graphics.stanford.edu/~seander/bithacks.html#ZerosOnRightMultLookup
http://marupeke296.com/TIPS_No17_Bit.html

binary logarithm algorithm based on
http://en.wikipedia.org/wiki/Binary_logarithm#Real_number

*/

#include "fastonebigheader.h"

const uint8_t lsb_64_table[64] =
{
   63, 30,  3, 32, 59, 14, 11, 33,
   60, 24, 50,  9, 55, 19, 21, 34,
   61, 29,  2, 53, 51, 23, 41, 18,
   56, 28,  1, 43, 46, 27,  0, 35,
   62, 31, 58,  4,  5, 49, 54,  6,
   15, 52, 12, 40,  7, 42, 45, 16,
   25, 57, 48, 13, 10, 39,  8, 44,
   20, 47, 38, 22, 17, 37, 36, 26
};
 
/**
 * bitScanForward
 * @author Matt Taylor (2003)
 * @param bb bitboard to scan
 * @precondition bb != 0
 * @return index (0..63) of least significant one bit
 */
int bitScanForward(uint64_t bb) {
   unsigned int folded;
   assert (bb != 0);
   bb ^= bb - 1;
   folded = (int) bb ^ (bb >> 32);
   return lsb_64_table[folded * 0x78291ACF >> 26];
}


// most significant bit position
// find the log base 2 of 32-bit v
static const uint8_t msb_MultiplyDeBruijnBitPosition[32] = {
	0, 9, 1, 10, 13, 21, 2, 29, 11, 14, 16, 18, 22, 25, 3, 30,
	8, 12, 20, 28, 15, 17, 24, 7, 19, 27, 23, 6, 26, 5, 4, 31
};
size_t msb8bit(uint8_t v)
{
	v |= v >> 1; // first round down to one less than a power of 2 
	v |= v >> 2;
	v |= v >> 4;
	return msb_MultiplyDeBruijnBitPosition[(uint32_t)(v * 0x07C4ACDDU) >> 27];
}
size_t msb16bit(uint16_t v) {
	v |= v >> 1; // first round down to one less than a power of 2 
	v |= v >> 2;
	v |= v >> 4;
	v |= v >> 8;
	return msb_MultiplyDeBruijnBitPosition[(uint32_t)(v * 0x07C4ACDDU) >> 27];
}
size_t msb32bit(uint32_t v)
{
	v |= v >> 1; // first round down to one less than a power of 2 
	v |= v >> 2;
	v |= v >> 4;
	v |= v >> 8;
	v |= v >> 16;
	return msb_MultiplyDeBruijnBitPosition[(uint32_t)(v * 0x07C4ACDDU) >> 27];
}

const uint8_t index64[64] = {
    0, 47,  1, 56, 48, 27,  2, 60,
   57, 49, 41, 37, 28, 16,  3, 61,
   54, 58, 35, 52, 50, 42, 21, 44,
   38, 32, 29, 23, 17, 11,  4, 62,
   46, 55, 26, 59, 40, 36, 15, 53,
   34, 51, 20, 43, 31, 22, 10, 45,
   25, 39, 14, 33, 19, 30,  9, 24,
   13, 18,  8, 12,  7,  6,  5, 63
};
 
/**
 * bitScanReverse
 * @authors Kim Walisch, Mark Dickinson
 * @param bb bitboard to scan
 * @precondition bb != 0
 * @return index (0..63) of most significant one bit
 */
int bitScanReverse(uint64_t bb) {
   const uint64_t debruijn64 = 0x03f79d71b4cb0a89ULL;
   assert (bb != 0);
   bb |= bb >> 1; 
   bb |= bb >> 2;
   bb |= bb >> 4;
   bb |= bb >> 8;
   bb |= bb >> 16;
   bb |= bb >> 32;
   return index64[(bb * debruijn64) >> 58];
}

// find the log2 of 32-bit integer v
// return value is fractional value
uint32_t ilog2_32(uint32_t v, size_t iteCnt, uint32_t* pIntPart)
{
	if (v == 0 || iteCnt > 28) {
		return (uint32_t)-1;
	}
	uint32_t resultBits = 0;
	size_t trailZeroCount = bitScanForward(v);
	size_t posMSB = msb32bit(v);
	size_t nFracBits = posMSB;
	*pIntPart = posMSB;
	if (posMSB == trailZeroCount) {
		return 0;
	}
	v >>= trailZeroCount;
	nFracBits -= trailZeroCount;

	for (size_t i=0; i<iteCnt; ++i) {
		while (v >= (1U<<16)) {
//			size_t rShifts = nFracBits - 15;
			size_t rShifts = msb16bit(v >> 16) + 1;
//			assert(rShifts == (msb16bit(v >> 16) + 1));
			uint32_t half = (1 << rShifts) - 1;
			v = (v + half) >> rShifts;
			nFracBits -= rShifts;
		}
		v *= v;
		nFracBits <<= 1;
		resultBits <<= 1;
		if (v >> (nFracBits+1)) {
			++resultBits;
			++nFracBits;
		}
	}
	return resultBits;
}

// find the log2 of 64-bit integer v
// return value is fixed-point fractional part (Q.iteCnt)
uint64_t ilog2_64(
	uint64_t	v,				// input integer value
	size_t		iteCnt,			// iteration count, output fractional part bit length
	uint32_t*	pIntPart		// pointer to store output integer part value
	)
{
//	assert(iteCnt <= 30);
	if (v == 0) {
		return (uint64_t)-1;
	}
	uint64_t resultBits = 0;
	size_t trailZeroCount = bitScanForward(v);
	size_t posMSB = bitScanReverse(v);
	*pIntPart = posMSB;
	if (posMSB == trailZeroCount) {
		return 0;
	}
	v >>= trailZeroCount;
	size_t nFracBits = posMSB - trailZeroCount;

	size_t i;
	for (i=0; i<iteCnt; ++i) {
		if (nFracBits >= 32u) {
			break;
		}
		v = v * (uint32_t)v;
		nFracBits <<= 1;
		size_t is2BitUp = (size_t)(v >> (nFracBits + 1u));
		nFracBits += is2BitUp;
		resultBits = (resultBits << 1) + is2BitUp;
	}
	for (; i<iteCnt; ++i) {
		size_t rShifts = nFracBits - 31u;
		assert(rShifts == (msb32bit(v >> 32) + 1u));
		v = v + (uint32_t)(1u << (rShifts - 1u));
		v >>= rShifts;
		nFracBits = (nFracBits << 1) - (rShifts << 1);
		resultBits <<= 1;
		v *= v;
		size_t is2BitUp = (size_t)(v >> (nFracBits + 1u));
		nFracBits += is2BitUp;
		resultBits += is2BitUp;
	}
	return resultBits;
}

// find the log2 of 64-bit fixed-point v
// return value is fixed-point log2 result (Q.iteCnt format)
int64_t fixed_log2(
	uint64_t	v,				// input fixed-point value
	size_t		fixedShift,		// input fraction bits count
	size_t		iteCnt			// iteration count is equal to output fraction bits count
	)
{
	uint32_t intPart;
	uint64_t fracBits = ilog2_64(v, iteCnt, &intPart);
	int64_t resultLog2Fixed = (int32_t)intPart - (int32_t)fixedShift;
	resultLog2Fixed <<= iteCnt;
	resultLog2Fixed += fracBits;
	return resultLog2Fixed;
}

// http://forum.osdev.org/viewtopic.php?f=13&t=26848
int64_t multiply64x32rshift(int64_t a, int32_t b, size_t rShifts)
{
	int sign = ((int32_t)(a >> 32) ^ b) >> 31;
	uint64_t ua = std::abs(a);
	uint32_t ub = std::abs(b);
	uint64_t ah = ua >> 32;
	uint64_t al = ua & 0xFFFFFFFF;
	uint64_t hl = ah * ub;
	uint64_t ll = al * ub;
	uint64_t result = (hl << (32 - rShifts)) + (ll >> rShifts);
	if (sign == 0) {
		return (int64_t)result;
	}else {
		return (int64_t)~result + 1;
	}
}

int16_t multiply16x8rshift(int16_t a, int8_t b, size_t rShifts)
{
	int sign = ((a >> 8) ^ b) >> 7;
	uint16_t ua = std::abs(a);
	uint8_t ub = std::abs(b);
	uint8_t ah = ua >> 8;
	uint8_t al = ua & 0xFF;
	uint16_t hl = ah * ub;
	uint16_t ll = al * ub;
	uint16_t result = (hl << (8 - rShifts)) + (ll >> rShifts);
	if (sign == 0) {
		return result;
	}else {
		return (int16_t)~result + 1;
	}
}

int main(int argc, char* argv[])
{
#if 0
	int64_t r = multiply16x8rshift(-12345, 123, 8);
	r = multiply64x32rshift(-1LL<<40, 1<<30, 20);
	uint32_t ip;
	uint64_t r = ilog2_64(17, 10, &ip);

	size_t iteCnt = 24;
	int64_t ret = fixed_log2(33, 15, iteCnt);
	double fret = ret / (double)(1LL << iteCnt);
#endif

	Timer t;

	// http://skyblueryu.blog54.fc2.com/blog-entry-27.html
#define M_LN2      0.69314718055994530941
#define INV_BASE2_LOGE_SHIFTS 31
	static const uint32_t invBase2LogE = (uint32_t)(M_LN2 * (double)(1U << INV_BASE2_LOGE_SHIFTS) + 0.5);
	static_assert(invBase2LogE == 0x58b90bfc, "err");

	printf("shifts maxerr(log2) avgerr(log2) maxerr(logE) avgerr(logE) elapsed_time\n");
	for (size_t nShifts=10; nShifts<=40; ++nShifts) {
		t.Start();
		double invDenomOutFixed = 1.0 / (double)(1LL << nShifts);
		double maxDFLog2 = 0.0;
		double sumDFLog2 = 0.0;
		double maxDFLogE = 0.0;
		double sumDFLogE = 0.0;
		size_t inputFixedShift = 16;	// input fixed point value's fractional part length
		double invDenomInputFixed = 1.0 / (1LL << inputFixedShift);
		int64_t end = 1ULL << 22;
		int64_t start = 1ULL << 0;
		for (int64_t i=start; i<end; ++i) {
			// convert input fixed to float
			double fv = i * invDenomInputFixed;
#if 1
			int64_t resultLog2Fixed = fixed_log2(i, inputFixedShift, nShifts);
			// change of base
			int64_t resultLogEFixed = multiply64x32rshift(resultLog2Fixed, invBase2LogE, INV_BASE2_LOGE_SHIFTS);
			// convert from fixed to float
			double resultLog2 = resultLog2Fixed * invDenomOutFixed;
			double resultLogE = resultLogEFixed * invDenomOutFixed;
#else
			double resultLog2 = fastlog2(fv);
			double resultLogE = fastlog(fv);
#endif

#if 1
			double ansLogE = log(fv);
			// change of base
			double ansLog2 = ansLogE / log(2.0);

			// diff
			double dfLogE = std::abs(ansLogE - resultLogE);
			double dfLog2 = std::abs(ansLog2 - resultLog2);
			maxDFLogE = std::max(maxDFLogE, dfLogE);
			sumDFLogE += dfLogE;
			maxDFLog2 = std::max(maxDFLog2, dfLog2);
			sumDFLog2 += dfLog2;
#endif
//			printf("%f %f %f %f\n", v, f1, f2, df);
		}
		int64_t count = end - start;
		double elapsed = t.Elapsed() / (double)t.GetFrequency();
		printf(
			"%d %.11f %.11f %.11f %.11f %f\n",
			nShifts, maxDFLog2, sumDFLog2/(count-1), maxDFLogE, sumDFLogE/(count-1),
			elapsed
		);
	}

	return 0;
}


