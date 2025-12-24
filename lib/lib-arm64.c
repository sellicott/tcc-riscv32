/*
 *  TCC runtime library for arm64.
 *
 *  Copyright (c) 2015 Edmund Grimley Evans
 *
 * Copying and distribution of this file, with or without modification,
 * are permitted in any medium without royalty provided the copyright
 * notice and this notice are preserved.  This file is offered as-is,
 * without any warranty.
 */

#ifdef __TINYC__
typedef signed char int8_t;
typedef unsigned char uint8_t;
typedef short int16_t;
typedef unsigned short uint16_t;
typedef int int32_t;
typedef unsigned uint32_t;
typedef long long int64_t;
typedef unsigned long long uint64_t;
void *memcpy(void*,void*,__SIZE_TYPE__);
#else
#include <stdint.h>
#include <string.h>
#endif

#if 0 
    //!defined __riscv && !defined __APPLE__
void __clear_cache(void *beg, void *end)
{
    __arm64_clear_cache(beg, end);
}
#endif

typedef struct {
    uint64_t x0, x1;
} u128_t;

static long double f3_zero(int sgn)
{
    long double f;
    u128_t x = { 0, (uint64_t)sgn << 63 };
    memcpy(&f, &x, 16);
    return f;
}

static long double f3_infinity(int sgn)
{
    long double f;
    u128_t x = { 0, (uint64_t)sgn << 63 | 0x7fff000000000000 };
    memcpy(&f, &x, 16);
    return f;
}

static long double f3_NaN(void)
{
    long double f;
#if 0
    // ARM's default NaN usually has just the top fraction bit set:
    u128_t x = {  0, 0x7fff800000000000 };
#else
    // GCC's library sets all fraction bits:
    u128_t x = { -1, 0x7fffffffffffffff };
#endif
    memcpy(&f, &x, 16);
    return f;
}

static int fp3_convert_NaN(long double *f, int sgn, u128_t mnt)
{
    u128_t x = { mnt.x0,
                 mnt.x1 | 0x7fff800000000000 | (uint64_t)sgn << 63 };
    memcpy(f, &x, 16);
    return 1;
}

static int fp3_detect_NaNs(long double *f,
                           int a_sgn, int a_exp, u128_t a,
                           int b_sgn, int b_exp, u128_t b)
{
    // Detect signalling NaNs:
    if (a_exp == 32767 && (a.x0 | a.x1 << 16) && !(a.x1 >> 47 & 1))
        return fp3_convert_NaN(f, a_sgn, a);
    if (b_exp == 32767 && (b.x0 | b.x1 << 16) && !(b.x1 >> 47 & 1))
        return fp3_convert_NaN(f, b_sgn, b);

    // Detect quiet NaNs:
    if (a_exp == 32767 && (a.x0 | a.x1 << 16))
        return fp3_convert_NaN(f, a_sgn, a);
    if (b_exp == 32767 && (b.x0 | b.x1 << 16))
        return fp3_convert_NaN(f, b_sgn, b);

    return 0;
}

static void f3_unpack(int *sgn, int32_t *exp, u128_t *mnt, long double f)
{
    u128_t x;
    memcpy(&x, &f, 16);
    *sgn = x.x1 >> 63;
    *exp = x.x1 >> 48 & 32767;
    x.x1 = x.x1 << 16 >> 16;
    if (*exp)
        x.x1 |= (uint64_t)1 << 48;
    else
        *exp = 1;
    *mnt = x;
}

static u128_t f3_normalise(int32_t *exp, u128_t mnt)
{
    int sh;
    if (!(mnt.x0 | mnt.x1))
        return mnt;
    if (!mnt.x1) {
        mnt.x1 = mnt.x0;
        mnt.x0 = 0;
        *exp -= 64;
    }
    for (sh = 32; sh; sh >>= 1) {
        if (!(mnt.x1 >> (64 - sh))) {
            mnt.x1 = mnt.x1 << sh | mnt.x0 >> (64 - sh);
            mnt.x0 = mnt.x0 << sh;
            *exp -= sh;
        }
    }
    return mnt;
}

static u128_t f3_sticky_shift(int32_t sh, u128_t x)
{
  if (sh >= 128) {
      x.x0 = !!(x.x0 | x.x1);
      x.x1 = 0;
      return x;
  }
  if (sh >= 64) {
      x.x0 = x.x1 | !!x.x0;
      x.x1 = 0;
      sh -= 64;
  }
  if (sh > 0) {
      x.x0 = x.x0 >> sh | x.x1 << (64 - sh) | !!(x.x0 << (64 - sh));
      x.x1 = x.x1 >> sh;
  }
  return x;
}

static long double f3_round(int sgn, int32_t exp, u128_t x)
{
    long double f;
    int error;

    if (exp > 0) {
        x = f3_sticky_shift(13, x);
    }
    else {
        x = f3_sticky_shift(14 - exp, x);
        exp = 0;
    }

    error = x.x0 & 3;
    x.x0 = x.x0 >> 2 | x.x1 << 62;
    x.x1 = x.x1 >> 2;

    if (error == 3 || ((error == 2) & (x.x0 & 1))) {
        if (!++x.x0) {
            ++x.x1;
            if (x.x1 == (uint64_t)1 << 48)
                exp = 1;
            else if (x.x1 == (uint64_t)1 << 49) {
                ++exp;
                x.x0 = x.x0 >> 1 | x.x1 << 63;
                x.x1 = x.x1 >> 1;
            }
        }
    }

    if (exp >= 32767)
        return f3_infinity(sgn);

    x.x1 = x.x1 << 16 >> 16 | (uint64_t)exp << 48 | (uint64_t)sgn << 63;
    memcpy(&f, &x, 16);
    return f;
}

static long double f3_add(long double fa, long double fb, int neg)
{
    u128_t a, b, x;
    int32_t a_exp, b_exp, x_exp;
    int a_sgn, b_sgn, x_sgn;
    long double fx;

    f3_unpack(&a_sgn, &a_exp, &a, fa);
    f3_unpack(&b_sgn, &b_exp, &b, fb);

    if (fp3_detect_NaNs(&fx, a_sgn, a_exp, a, b_sgn, b_exp, b))
        return fx;

    b_sgn ^= neg;

    // Handle infinities and zeroes:
    if (a_exp == 32767 && b_exp == 32767 && a_sgn != b_sgn)
        return f3_NaN();
    if (a_exp == 32767)
        return f3_infinity(a_sgn);
    if (b_exp == 32767)
        return f3_infinity(b_sgn);
    if (!(a.x0 | a.x1 | b.x0 | b.x1))
        return f3_zero(a_sgn & b_sgn);

    a.x1 = a.x1 << 3 | a.x0 >> 61;
    a.x0 = a.x0 << 3;
    b.x1 = b.x1 << 3 | b.x0 >> 61;
    b.x0 = b.x0 << 3;

    if (a_exp <= b_exp) {
        a = f3_sticky_shift(b_exp - a_exp, a);
        a_exp = b_exp;
    }
    else {
        b = f3_sticky_shift(a_exp - b_exp, b);
        b_exp = a_exp;
    }

    x_sgn = a_sgn;
    x_exp = a_exp;
    if (a_sgn == b_sgn) {
        x.x0 = a.x0 + b.x0;
        x.x1 = a.x1 + b.x1 + (x.x0 < a.x0);
    }
    else {
        x.x0 = a.x0 - b.x0;
        x.x1 = a.x1 - b.x1 - (x.x0 > a.x0);
        if (x.x1 >> 63) {
            x_sgn ^= 1;
            x.x0 = -x.x0;
            x.x1 = -x.x1 - !!x.x0;
        }
    }

    if (!(x.x0 | x.x1))
        return f3_zero(0);

    x = f3_normalise(&x_exp, x);

    return f3_round(x_sgn, x_exp + 12, x);
}

long double __addtf3(long double a, long double b)
{
    return f3_add(a, b, 0);
}

long double __subtf3(long double a, long double b)
{
    return f3_add(a, b, 1);
}

long double __multf3(long double fa, long double fb)
{
    u128_t a, b, x;
    int32_t a_exp, b_exp, x_exp;
    int a_sgn, b_sgn, x_sgn;
    long double fx;

    f3_unpack(&a_sgn, &a_exp, &a, fa);
    f3_unpack(&b_sgn, &b_exp, &b, fb);

    if (fp3_detect_NaNs(&fx, a_sgn, a_exp, a, b_sgn, b_exp, b))
        return fx;

    // Handle infinities and zeroes:
    if ((a_exp == 32767 && !(b.x0 | b.x1)) ||
        (b_exp == 32767 && !(a.x0 | a.x1)))
        return f3_NaN();
    if (a_exp == 32767 || b_exp == 32767)
        return f3_infinity(a_sgn ^ b_sgn);
    if (!(a.x0 | a.x1) || !(b.x0 | b.x1))
        return f3_zero(a_sgn ^ b_sgn);

    a = f3_normalise(&a_exp, a);
    b = f3_normalise(&b_exp, b);

    x_sgn = a_sgn ^ b_sgn;
    x_exp = a_exp + b_exp - 16352;

    {
        // Convert to base (1 << 30), discarding bottom 6 bits, which are zero,
        // so there are (32, 30, 30, 30) bits in (a3, a2, a1, a0):
        uint64_t a0 = a.x0 << 28 >> 34;
        uint64_t b0 = b.x0 << 28 >> 34;
        uint64_t a1 = a.x0 >> 36 | a.x1 << 62 >> 34;
        uint64_t b1 = b.x0 >> 36 | b.x1 << 62 >> 34;
        uint64_t a2 = a.x1 << 32 >> 34;
        uint64_t b2 = b.x1 << 32 >> 34;
        uint64_t a3 = a.x1 >> 32;
        uint64_t b3 = b.x1 >> 32;
        // Use 16 small multiplications and additions that do not overflow:
        uint64_t x0 = a0 * b0;
        uint64_t x1 = (x0 >> 30) + a0 * b1 + a1 * b0;
        uint64_t x2 = (x1 >> 30) + a0 * b2 + a1 * b1 + a2 * b0;
        uint64_t x3 = (x2 >> 30) + a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0;
        uint64_t x4 = (x3 >> 30) + a1 * b3 + a2 * b2 + a3 * b1;
        uint64_t x5 = (x4 >> 30) + a2 * b3 + a3 * b2;
        uint64_t x6 = (x5 >> 30) + a3 * b3;
        // We now have (64, 30, 30, ...) bits in (x6, x5, x4, ...).
        // Take the top 128 bits, setting bottom bit if any lower bits were set:
        uint64_t y0 = (x5 << 34 | x4 << 34 >> 30 | x3 << 34 >> 60 |
                       !!(x3 << 38 | (x2 | x1 | x0) << 34));
        uint64_t y1 = x6;
        // Top bit may be zero. Renormalise:
        if (!(y1 >> 63)) {
            y1 = y1 << 1 | y0 >> 63;
            y0 = y0 << 1;
            --x_exp;
        }
        x.x0 = y0;
        x.x1 = y1;
    }

    return f3_round(x_sgn, x_exp, x);
}

long double __divtf3(long double fa, long double fb)
{
    u128_t a, b, x;
    int32_t a_exp, b_exp, x_exp;
    int a_sgn, b_sgn, x_sgn, i;
    long double fx;

    f3_unpack(&a_sgn, &a_exp, &a, fa);
    f3_unpack(&b_sgn, &b_exp, &b, fb);

    if (fp3_detect_NaNs(&fx, a_sgn, a_exp, a, b_sgn, b_exp, b))
        return fx;

    // Handle infinities and zeroes:
    if ((a_exp == 32767 && b_exp == 32767) ||
        (!(a.x0 | a.x1) && !(b.x0 | b.x1)))
        return f3_NaN();
    if (a_exp == 32767 || !(b.x0 | b.x1))
        return f3_infinity(a_sgn ^ b_sgn);
    if (!(a.x0 | a.x1) || b_exp == 32767)
        return f3_zero(a_sgn ^ b_sgn);

    a = f3_normalise(&a_exp, a);
    b = f3_normalise(&b_exp, b);

    x_sgn = a_sgn ^ b_sgn;
    x_exp = a_exp - b_exp + 16395;

    a.x0 = a.x0 >> 1 | a.x1 << 63;
    a.x1 = a.x1 >> 1;
    b.x0 = b.x0 >> 1 | b.x1 << 63;
    b.x1 = b.x1 >> 1;
    x.x0 = 0;
    x.x1 = 0;
    for (i = 0; i < 116; i++) {
        x.x1 = x.x1 << 1 | x.x0 >> 63;
        x.x0 = x.x0 << 1;
        if (a.x1 > b.x1 || (a.x1 == b.x1 && a.x0 >= b.x0)) {
            a.x1 = a.x1 - b.x1 - (a.x0 < b.x0);
            a.x0 = a.x0 - b.x0;
            x.x0 |= 1;
        }
        a.x1 = a.x1 << 1 | a.x0 >> 63;
        a.x0 = a.x0 << 1;
    }
    x.x0 |= !!(a.x0 | a.x1);

    x = f3_normalise(&x_exp, x);

    return f3_round(x_sgn, x_exp, x);
}

long double __extendsftf2(float f)
{
    long double fx;
    u128_t x;
    uint32_t a;
    uint64_t aa;
    memcpy(&a, &f, 4);
    aa = a;
    x.x0 = 0;
    if (!(a << 1))
        x.x1 = aa << 32;
    else if (a << 1 >> 24 == 255)
        x.x1 = (0x7fff000000000000 | aa >> 31 << 63 | aa << 41 >> 16 |
                (uint64_t)!!(a << 9) << 47);
    else if (a << 1 >> 24 == 0) {
        uint64_t adj = 0;
        while (!(a << 1 >> 1 >> (23 - adj)))
          adj++;
        x.x1 = aa >> 31 << 63 | (16256 - adj + 1) << 48 | aa << adj << 41 >> 16;
    } else
        x.x1 = (aa >> 31 << 63 | ((aa >> 23 & 255) + 16256) << 48 |
                aa << 41 >> 16);
    memcpy(&fx, &x, 16);
    return fx;
}

long double __extenddftf2(double f)
{
    long double fx;
    u128_t x;
    uint64_t a;
    memcpy(&a, &f, 8);
    x.x0 = a << 60;
    if (!(a << 1))
        x.x1 = a;
    else if (a << 1 >> 53 == 2047)
        x.x1 = (0x7fff000000000000 | a >> 63 << 63 | a << 12 >> 16 |
                (uint64_t)!!(a << 12) << 47);
    else if (a << 1 >> 53 == 0) {
        uint64_t adj = 0;
        while (!(a << 1 >> 1 >> (52 - adj)))
          adj++;
        x.x0 <<= adj;
        x.x1 = a >> 63 << 63 | (15360 - adj + 1) << 48 | a << adj << 12 >> 16;
    } else
        x.x1 = a >> 63 << 63 | ((a >> 52 & 2047) + 15360) << 48 | a << 12 >> 16;
    memcpy(&fx, &x, 16);
    return fx;
}

float __trunctfsf2(long double f)
{
    u128_t mnt;
    int32_t exp;
    int sgn;
    uint32_t x;
    float fx;

    f3_unpack(&sgn, &exp, &mnt, f);

    if (exp == 32767 && (mnt.x0 | mnt.x1 << 16))
        x = 0x7fc00000 | (uint32_t)sgn << 31 | (mnt.x1 >> 25 & 0x007fffff);
    else if (exp > 16510)
        x = 0x7f800000 | (uint32_t)sgn << 31;
    else if (exp < 16233)
        x = (uint32_t)sgn << 31;
    else {
        exp -= 16257;
        x = mnt.x1 >> 23 | !!(mnt.x0 | mnt.x1 << 41);
        if (exp < 0) {
            x = x >> -exp | !!(x << (32 + exp));
            exp = 0;
        }
        if ((x & 3) == 3 || (x & 7) == 6)
            x += 4;
        x = ((x >> 2) + (exp << 23)) | (uint32_t)sgn << 31;
    }
    memcpy(&fx, &x, 4);
    return fx;
}

double __trunctfdf2(long double f)
{
    u128_t mnt;
    int32_t exp;
    int sgn;
    uint64_t x;
    double fx;

    f3_unpack(&sgn, &exp, &mnt, f);

    if (exp == 32767 && (mnt.x0 | mnt.x1 << 16))
        x = (0x7ff8000000000000 | (uint64_t)sgn << 63 |
             mnt.x1 << 16 >> 12 | mnt.x0 >> 60);
    else if (exp > 17406)
        x = 0x7ff0000000000000 | (uint64_t)sgn << 63;
    else if (exp < 15308)
        x = (uint64_t)sgn << 63;
    else {
        exp -= 15361;
        x = mnt.x1 << 6 | mnt.x0 >> 58 | !!(mnt.x0 << 6);
        if (exp < 0) {
            x = x >> -exp | !!(x << (64 + exp));
            exp = 0;
        }
        if ((x & 3) == 3 || (x & 7) == 6)
            x += 4;
        x = ((x >> 2) + ((uint64_t)exp << 52)) | (uint64_t)sgn << 63;
    }
    memcpy(&fx, &x, 8);
    return fx;
}

int32_t __fixtfsi(long double fa)
{
    u128_t a;
    int32_t a_exp;
    int a_sgn;
    int32_t x;
    f3_unpack(&a_sgn, &a_exp, &a, fa);
    if (a_exp < 16369)
        return 0;
    if (a_exp > 16413)
        return a_sgn ? -0x80000000 : 0x7fffffff;
    x = a.x1 >> (16431 - a_exp);
    return a_sgn ? -x : x;
}

int64_t __fixtfdi(long double fa)
{
    u128_t a;
    int32_t a_exp;
    int a_sgn;
    int64_t x;
    f3_unpack(&a_sgn, &a_exp, &a, fa);
    if (a_exp < 16383)
        return 0;
    if (a_exp > 16445)
        return a_sgn ? -0x8000000000000000 : 0x7fffffffffffffff;
    x = (a.x1 << 15 | a.x0 >> 49) >> (16446 - a_exp);
    return a_sgn ? -x : x;
}

uint32_t __fixunstfsi(long double fa)
{
    u128_t a;
    int32_t a_exp;
    int a_sgn;
    f3_unpack(&a_sgn, &a_exp, &a, fa);
    if (a_sgn || a_exp < 16369)
        return 0;
    if (a_exp > 16414)
        return -1;
    return a.x1 >> (16431 - a_exp);
}

uint64_t __fixunstfdi(long double fa)
{
    u128_t a;
    int32_t a_exp;
    int a_sgn;
    f3_unpack(&a_sgn, &a_exp, &a, fa);
    if (a_sgn || a_exp < 16383)
        return 0;
    if (a_exp > 16446)
        return -1;
    return (a.x1 << 15 | a.x0 >> 49) >> (16446 - a_exp);
}

long double __floatsitf(int32_t a)
{
    int sgn = 0;
    int exp = 16414;
    uint32_t mnt = a;
    u128_t x = { 0, 0 };
    long double f;
    int i;
    if (a) {
        if (a < 0) {
            sgn = 1;
            mnt = -mnt;
        }
        for (i = 16; i; i >>= 1)
            if (!(mnt >> (32 - i))) {
                mnt <<= i;
                exp -= i;
            }
        x.x1 = ((uint64_t)sgn << 63 | (uint64_t)exp << 48 |
                (uint64_t)(mnt << 1) << 16);
    }
    memcpy(&f, &x, 16);
    return f;
}

long double __floatditf(int64_t a)
{
    int sgn = 0;
    int exp = 16446;
    uint64_t mnt = a;
    u128_t x = { 0, 0 };
    long double f;
    int i;
    if (a) {
        if (a < 0) {
            sgn = 1;
            mnt = -mnt;
        }
        for (i = 32; i; i >>= 1)
            if (!(mnt >> (64 - i))) {
                mnt <<= i;
                exp -= i;
            }
        x.x0 = mnt << 49;
        x.x1 = (uint64_t)sgn << 63 | (uint64_t)exp << 48 | mnt << 1 >> 16;
    }
    memcpy(&f, &x, 16);
    return f;
}

long double __floatunsitf(uint32_t a)
{
    int exp = 16414;
    uint32_t mnt = a;
    u128_t x = { 0, 0 };
    long double f;
    int i;
    if (a) {
        for (i = 16; i; i >>= 1)
            if (!(mnt >> (32 - i))) {
                mnt <<= i;
                exp -= i;
            }
        x.x1 = (uint64_t)exp << 48 | (uint64_t)(mnt << 1) << 16;
    }
    memcpy(&f, &x, 16);
    return f;
}

long double __floatunditf(uint64_t a)
{
    int exp = 16446;
    uint64_t mnt = a;
    u128_t x = { 0, 0 };
    long double f;
    int i;
    if (a) {
        for (i = 32; i; i >>= 1)
            if (!(mnt >> (64 - i))) {
                mnt <<= i;
                exp -= i;
            }
        x.x0 = mnt << 49;
        x.x1 = (uint64_t)exp << 48 | mnt << 1 >> 16;
    }
    memcpy(&f, &x, 16);
    return f;
}

static int f3_cmp(long double fa, long double fb)
{
    u128_t a, b;
    memcpy(&a, &fa, 16);
    memcpy(&b, &fb, 16);
    return (!(a.x0 | a.x1 << 1 | b.x0 | b.x1 << 1) ? 0 :
            ((a.x1 << 1 >> 49 == 0x7fff && (a.x0 | a.x1 << 16)) ||
             (b.x1 << 1 >> 49 == 0x7fff && (b.x0 | b.x1 << 16))) ? 2 :
            a.x1 >> 63 != b.x1 >> 63 ? (int)(b.x1 >> 63) - (int)(a.x1 >> 63) :
            a.x1 < b.x1 ? (int)(a.x1 >> 63 << 1) - 1 :
            a.x1 > b.x1 ? 1 - (int)(a.x1 >> 63 << 1) :
            a.x0 < b.x0 ? (int)(a.x1 >> 63 << 1) - 1 :
            b.x0 < a.x0 ? 1 - (int)(a.x1 >> 63 << 1) : 0);
}

int __eqtf2(long double a, long double b)
{
    return !!f3_cmp(a, b);
}

int __netf2(long double a, long double b)
{
    return !!f3_cmp(a, b);
}

int __lttf2(long double a, long double b)
{
    return f3_cmp(a, b);
}

int __letf2(long double a, long double b)
{
    return f3_cmp(a, b);
}

int __gttf2(long double a, long double b)
{
    return -f3_cmp(b, a);
}

int __getf2(long double a, long double b)
{
    return -f3_cmp(b, a);
}

#include <stdio.h>
void __floatundef(void)
{
    printf("[lib-arm64] undefined floating point operation called\n");
}


void float_warn(const char *func)
{
    printf("[lib-arm64] dubious floating point operation %s\n", func);
}

// only add single and double floating point ops if we are in riscv32 mode
// #ifdef TCC_RISCV_ilp32

// generate a canonical single precision NaN value
static float f1_NaN(void)
{  
    float f;
    uint32_t bin = 0x7fc00000U;
    // the risc-v canonical NaN has a positive sign bit and the
    // mantissa MSB set, all other mantissa bits are 0.
    memcpy(&f, &bin, sizeof(bin));
    return f;
}

// generate a single precision infinity value
// sgn must be 1 or 0
static float f1_infinity(uint32_t sgn)
{  
    float f;
    // set the sign bit from the input, and all exponent bits set
    // mantissa bits are 0.
    uint32_t bin = (sgn << 31) | (255 << 23);
    memcpy(&f, &bin, sizeof(f));
    return f;
}

// generate a single precision zero value
// sgn must be 1 or 0 
static float f1_zero(uint32_t sgn)
{  
    float f;
    // set the sign bit from the input, and all bits set to 0.
    uint32_t bin = (sgn << 31);
    memcpy(&f, &bin, sizeof(f));
    return f;
}


// return 1 if either of the floating point values are a NaN, 0 if not.
// In the case of a NaN, the input parameter f will hold the appropriate NaN
//
// from the risc-v manual on floating point, when a NaN is generated, it produces
// the "canonical NaN" which is a signalling NaN with all other bits as zero.
//
// Evaluated by checking "a" first, then "b"
// using the same function signature as fp3_detect_NaNs for future compatability
static int f1_detect_NaNs(float *f, 
                          uint32_t a_sgn, uint8_t a_exp, uint32_t a_mnt,
                          uint32_t b_sgn, uint8_t b_exp, uint32_t b_mnt)
{
    // all NaNs have an exponent of 255 and at least one mantissa bit set
    if ( (a_exp == 255 && a_mnt) 
      || (b_exp == 255 && b_mnt)) {
        *f = f1_NaN();
        return 1;
    }

    // no NaNs detected
    return 0;
}

// Right shift the single precision floating point mantissa.
// The mantissa should have three bits of padding for G, R, and S bits.
// Two of the shifted out bits of the aligned significand are retained as
// guard (G) and Round (R) bits. So for p bit significands, the effective width
// of aligned significand must be p + 2 bits. Append a third bit, namely the
// sticky bit (S), at the right end of the aligned significand.
// The sticky bit is the logical OR of all shifted out bits.
static uint32_t f1_sticky_shift(uint32_t sh, uint32_t mnt)
{
    // return the shifted output and the sticky bit
    // obtained by left shifting out all of the bits "above" the ones
    // that went off the end.
    return (mnt >> sh) | !!(mnt << (31 - sh));
}

static void sf_unpack(uint32_t *sgn, uint8_t *exp, uint32_t *mnt, float f)
{
    uint32_t x;
    memcpy(&x, &f, sizeof(f));
    *sgn = x >> 31;
    *exp = (x >> 23 & 0xff);
    *mnt = x & ((1<<23)-1);
}

static void print_float(float f){
    uint32_t bin;
    memcpy(&bin, &f, sizeof(f));

    printf("raw: %llx\n", bin);

    uint32_t sign     = !!(bin & ( 1L<<31));
    uint8_t  exponent  =  ((bin & (0x7FFL<<23)) >> 23);
    uint32_t mantissa =   (bin & 0x7fffffL);
    printf("value: %f\n", f);
    printf("float: sign: %d, exponent: %d, mantissa: %06x\n",
            sign, exponent-127, mantissa);
}

static void print_binary(uint32_t x, uint8_t len) {
    char buffer[33] = {'\0'};
    if (len > 31) len = 31;
    
    for (int i = len; i >= 0; --i) {
        uint32_t mask = (1 << i);
        int val = x & mask;
        buffer[len-i] = val ? '1':'0';
    }
    printf("%s\n", buffer);
}

// add two single precision floating point numbers, based on f3_add function
static float f1_add(float a, float b, int neg)
{
    // find the components
    uint32_t a_sgn;
    uint8_t  a_exp;
    uint32_t a_mnt;

    uint32_t b_sgn;
    uint8_t  b_exp;
    uint32_t b_mnt;

    uint32_t x_sgn;
    uint8_t  x_exp;
    uint32_t x_mnt;

    printf("input: a: %f b: %f\n", a, b);

    sf_unpack(&a_sgn, &a_exp, &a_mnt, a);
    sf_unpack(&b_sgn, &b_exp, &b_mnt, b);

    // handle NaN inputs
    // Currently does not propogate input NaNs, generates a canonical NaN
    if ( (a_exp == 255 && a_mnt) || (b_exp == 255 && b_mnt) )
        return f1_NaN();

    // flip the sign on b if we are subtracting
    b_sgn ^= neg;

    // Handle infinities and zeroes:
    // infinity - infinity = NaN
    if (a_exp == 255 && b_exp == 255 && a_sgn != b_sgn)
        return f1_NaN();

    // infinity +- C = infinity
    if (a_exp == 255)
        return f1_infinity(a_sgn);

    // C +- infinity = infinity
    if (b_exp == 255)
        return f1_infinity(b_sgn);

    // if both inputs are zero, return a zero of the appropriate sign
    // zeros are encoded as all zero exponents and mantissas
    if (!(a_exp | b_exp) && !(a_mnt | b_mnt))
        return f1_zero(a_sgn & b_sgn);

    // implement FP addition algorighm from
    // https://users.encs.concordia.ca/~asim/COEN_6501/Lecture_Notes/L4_Slides.pdf

    // 1) Compare the exponents of two numbers for and calculate the absolute
    //    value of difference between the two exponents.
    //    Take the larger exponent as the tentative exponent of the result.
    // 2) Shift the significand of the number with the smaller exponent,
    //    right through a number of bit positions that is equal to the exponent
    //    difference.

    // before sticky shifting, we need to make room for the gaurd, round, and
    // sticky bits (G, R, and S). We also need to add back the leading '1'.
    a_mnt = ((1 << 23) | a_mnt) << 3;
    b_mnt = ((1 << 23) | b_mnt) << 3;

    // do steps 1 and 2
    // return the shifted output and the sticky bit
    // obtained by left shifting out all of the bits "above" the ones
    // that went off the end.
    int sh = a_exp - b_exp;
    printf("norm shift %d\n", sh);
    if(sh < 0) {
        sh = -sh;
        a_mnt = (a_mnt >> sh) | !!(a_mnt << (31 - sh));
        a_exp = b_exp;
    }
    else {
        b_mnt = (b_mnt >> sh) | !!(b_mnt << (31 - sh));
        b_exp = a_exp;
    }
    // initial output values
    x_sgn = a_sgn;
    x_exp = a_exp;

    printf("common exponent: %d\n", x_exp);
    printf("normed mantissas: a: %06x, b: %06x\n", a_mnt, b_mnt);

    // 3) Add/subtract the two signed-magnitude significands using a p + 3 bit
    //    adder. Let the result of this is SUM.

    // if the signs are the same, we can do addition
    if (a_sgn == b_sgn) {
        printf("addition\n");
        printf("a: ");
        print_binary(a_mnt, 27);
        printf("b: ");
        print_binary(b_mnt, 27);
        x_mnt = a_mnt + b_mnt;
        printf("x: ");
        print_binary(x_mnt, 27);

        // check for cout overflow (1 bit above the leading bit)
        if (x_mnt >> 27 ) {
            printf("cout overflow 1\n");
            x_mnt >>= 1;
            x_exp += 1;

            printf("x: ");
            print_binary(x_mnt, 27);
        }
    }
    // otherwise we need to subtract
    else {
        x_mnt =  a_mnt -  b_mnt;
        printf("sub: %06x - %06x = %06x\n", a_mnt, b_mnt, x_mnt);
        // check for the result's sign changing
        if (x_mnt >> 31) {
            x_sgn ^= 1;
            x_mnt = -x_mnt;
        }
        
        // check for the mantissa's being equal -> generating a zero
        if (!x_mnt)
            return f1_zero(0);

        // check for leading zeros and left shift until normalized
        while ( !(x_mnt >> 26) ) {
            x_mnt = x_mnt << 1; // right shift so that there is a 1 in the 23rd bit
            x_exp -= 1;         // adjust exponent accordingly
            printf("[f1_add] exp: %d, mnt: %06x\n", x_exp, x_mnt);
        }
    }

    // Shift down over G and the old R, reset the sticky bit 
    x_mnt = ( (x_mnt >> 1) | !!(x_mnt >> 3) );
    printf("shift down, reset sticky bit\n");
    printf("x: ");
    print_binary(x_mnt, 26);

    // round the resulting output
    // R * (M0 + S)
    if ( (x_mnt & 0x2) && ((x_mnt & 0x4) || (x_mnt & 0x1)) ) {
        printf("rounding\n");
        x_mnt += 0x4;

        printf("x: ");
        print_binary(x_mnt, 26);
        // check for cout overflow (1 bit above the leading bit)
        if (x_mnt >> 26 ) {
            printf("cout overflow 2\n");
            x_mnt >>= 1;
            x_exp += 1;

            printf("x: ");
            print_binary(x_mnt, 26);
        }
    }

    // get rid of S and R
    x_mnt >>= 2;
    printf("x: ");
    print_binary(x_mnt, 23);

    uint32_t o_bin =
              ((uint32_t) (x_sgn & 0x01)     << 31)
            | ((uint32_t) (x_exp & 0xff)     << 23)
            | ((uint32_t) (x_mnt & 0x7fffff) <<  0);

    float o_float;
    memcpy(&o_float, &o_bin, sizeof(o_bin));

    print_float(o_float);
    printf("output: %f\n\n", o_float);

    return o_float;
}

// returns 1 if a > b, -1 if b < a, 0 if equal
static int f1_cmp(float a, float b)
{
    // find the components
    uint32_t a_sgn;
    uint8_t  a_exp;
    uint32_t a_mnt;

    uint32_t b_sgn;
    uint8_t  b_exp;
    uint32_t b_mnt;

    sf_unpack(&a_sgn, &a_exp, &a_mnt, a);
    sf_unpack(&b_sgn, &b_exp, &b_mnt, b);

    // if the signs differ, return -1 if a is negative, 1 otherwise
    if (a_sgn ^ b_sgn)
        return (a_sgn) ? -1 : 1;

    // if the exponents differ, return -1 if a has the smaller exponent
    int sh = a_exp - b_exp;
    if (sh != 0)
        return (sh < 0) ? -1 : 1;

    // if the mantissas differ, return -1 if a has the smaller mantissa
    if (a_mnt != b_mnt)
        return (a_mnt < b_mnt) ? -1 : 1;

    // otherwise they are both the same
    return 0;
}

// handle single floating point math
float __addsf3(float a, float b)
{
    return f1_add(a, b, 0);
}

float __subsf3(float a, float b)
{
    return f1_add(a, b, 1);
}

float __mulsf3(float a, float b)
{
    float_warn(__FUNCTION__);
    return (float) -1;
}

float __divsf3(float a, float b)
{
    float_warn(__FUNCTION__);
    return (float) -1;
}

float __adddf3(float a, float b)
{
    float_warn(__FUNCTION__);
    return (float) -1;
}

// handle double floating point math
double __subdf3(double a, double b)
{
    float_warn(__FUNCTION__);
    return (double) -1;
}

double __muldf3(double a, double b)
{
    float_warn(__FUNCTION__);
    return (double) -1;
}

double __divdf3(double a, double b)
{
    float_warn(__FUNCTION__);
    return (double) -1;
}


// single floating point comparisons
int __ltsf2(float a, float b)
{
    float_warn(__FUNCTION__);
    return f1_cmp(a, b);
}

int __lesf2(float a, float b)
{
    float_warn(__FUNCTION__);
    return f1_cmp(a, b);
}

int __gtsf2(float a, float b)
{
    float_warn(__FUNCTION__);
    return -f1_cmp(b, a);
}

int __gesf2(float a, float b)
{
    float_warn(__FUNCTION__);
    return -f1_cmp(b, a);
}

int __eqsf2(float a, float b)
{
    float_warn(__FUNCTION__);
    return !!f1_cmp(a, b);
}

int __nesf2(float a, float b)
{
    float_warn(__FUNCTION__);
    return !!!f1_cmp(a, b);
}

// double floating point comparisons
int __ledf2(float a, float b)
{
    float_warn(__FUNCTION__);
    return f3_cmp(a, b);
}

int __ltdf2(float a, float b)
{
    float_warn(__FUNCTION__);
    return f3_cmp(a, b);
}

int __gedf2(float a, float b)
{
    float_warn(__FUNCTION__);
    return -f3_cmp(b, a);
}

int __gtdf2(float a, float b)
{
    float_warn(__FUNCTION__);
    return -f3_cmp(b, a);
}

int __eqdf2(float a, float b)
{
    float_warn(__FUNCTION__);
    return !!f3_cmp(a, b);
}

int __nedf2(float a, float b)
{
    float_warn(__FUNCTION__);
    return !!!f3_cmp(a, b);
}

// floating point conversion functions
float __floatdisf(long i)
{
    float_warn(__FUNCTION__);
    return (float) -1;
}

double __floatdidf(long i)
{
    float_warn(__FUNCTION__);
    return (double) -1;
}

// floating point extension functions
// convert float -> double
double __extendsfdf2(float a)
{
    uint32_t in_bin;
    memcpy(&in_bin, &a, sizeof(a));
    
    uint32_t sign     = !!(in_bin & 0x80000000);
    uint32_t mantissa =   (in_bin & 0x007fffff);
    uint32_t exponent =  ((in_bin & 0x7f800000) >> 23);
    exponent = (exponent - 127) + 1023;

    uint64_t out_bin =
          ((uint64_t) sign     << 63)
        | ((uint64_t) exponent << 52)
        | ((uint64_t) mantissa << 29);

    double out_double;
    memcpy(&out_double, &out_bin, sizeof(out_bin));
    return out_double;

    // gcc compiled form of the previous C code
    /*
    asm volatile("slli    a1, a0, 1   \n\t"
        "lui     a3, 524288  \n\t"
        "slli    a2, a0, 29  \n\t"
        "and     a3, a3, a0  \n\t"
        "slli    a0, a0, 9   \n\t"
        "srli    a0, a0, 12  \n\t"
        "srli    a1, a1, 24  \n\t"
        "addi    a1, a1, 896 \n\t"
        "slli    a1, a1, 20  \n\t"
        "or      a0, a0, a3  \n\t"
        "or      a1, a1, a0  \n\t"
        "mv      a0, a2"
        : :
        : "a0", "a1", "a2", "a3");
    */
}

//#endif 

