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

https://chessprogramming.wikispaces.com/BitScan
http://graphics.stanford.edu/~seander/bithacks.html#ZerosOnRightMultLookup
http://marupeke296.com/TIPS_No17_Bit.html

algorithm based on
http://en.wikipedia.org/wiki/Binary_logarithm#Real_number

*/

// #include "fastonebigheader.h"

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
size_t msb8bit(uint16_t v)
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
	assert(iteCnt <= 28);
	if (v == 0) {
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
			uint32_t rShifts = msb16bit(v >> 16) + 1;
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
uint32_t ilog2_64(uint64_t v, size_t iteCnt, uint32_t* pIntPart)
{
	assert(iteCnt <= 30);
	if (v == 0) {
		return (uint32_t)-1;
	}
	uint32_t resultBits = 0;
	size_t trailZeroCount = bitScanForward(v);
	size_t posMSB = bitScanReverse(v);
	size_t nFracBits = posMSB;
	*pIntPart = posMSB;
	if (posMSB == trailZeroCount) {
		return 0;
	}
	v >>= trailZeroCount;
	nFracBits -= trailZeroCount;

	for (size_t i=0; i<iteCnt; ++i) {
		while (v >= (1ULL<<32)) {
			uint32_t rShifts = msb32bit(v >> 32) + 1;
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

int main(int argc, char* argv[])
{

	Timer t;
	t.Start();

	// http://skyblueryu.blog54.fc2.com/blog-entry-27.html
#define M_LN2      0.69314718055994530941
#define INV_BASE2_LOGE_SHIFTS 31
	static const uint32_t invBase2LogE = (uint32_t)(M_LN2 * (double)(1U << INV_BASE2_LOGE_SHIFTS) + 0.5);
	static_assert(invBase2LogE == 0x58b90bfc, "err");

	printf("shifts maxerr(log2) avgerr(log2) maxerr(logE) avgerr(logE)\n");
	for (size_t nShifts=8; nShifts<=27; ++nShifts) {
		double invDenomOutFixed = 1.0 / (double)(1 << nShifts);
		double maxDFLog2 = 0.0;
		double sumDFLog2 = 0.0;
		double maxDFLogE = 0.0;
		double sumDFLogE = 0.0;
		size_t inputFixedShift = 8;	// input fixed point value's fractional part length
		double invDenomInputFixed = 1.0 / (1LL << inputFixedShift);
		int64_t end = 1ULL << 26;
		int64_t start = std::max((1LL << inputFixedShift), end - (1 << 16)); // must start from 1.0
		for (int64_t i=start; i<end; ++i) {
			uint32_t intPart;
			uint32_t frac32 = ilog2_64(i, nShifts, &intPart);
			// adjust integer part of the result with input fixed point shifts
			// output value's fractional part length is nShifts
			uint32_t resultLog2Fixed = ((intPart - inputFixedShift) << nShifts) | frac32;
			// change of base
			uint32_t resultLogEFixed = ((uint64_t)resultLog2Fixed * invBase2LogE) >> INV_BASE2_LOGE_SHIFTS;
			// convert from fixed to float
			double resultLog2 = resultLog2Fixed * invDenomOutFixed;
			double resultLogE = resultLogEFixed * invDenomOutFixed;

			// convert input fixed to float
			double v = i * invDenomInputFixed;
			double ansLogE = log(v);
			// change of base
			double ansLog2 = ansLogE / log(2.0);

			// diff
			double dfLogE = abs(ansLogE - resultLogE);
			double dfLog2 = abs(ansLog2 - resultLog2);
			maxDFLogE = std::max(maxDFLogE, dfLogE);
			sumDFLogE += dfLogE;
			maxDFLog2 = std::max(maxDFLog2, dfLog2);
			sumDFLog2 += dfLog2;
//			printf("%f %f %f %f\n", v, f1, f2, df);
		}
		int64_t count = end - start;
		printf(
			"%d %.9f %.9f %.9f %.9f\n",
			nShifts, maxDFLog2, sumDFLog2/(count-1), maxDFLogE, sumDFLogE/(count-1)
		);
	}

	printf("%f\n", t.Elapsed() / (double)t.GetFrequency());

	return 0;
}


