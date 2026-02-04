// fp.c - PDP-11 floating point operations
//
// The floating-point emulation code here is
// just enough to allow 2.11BSD binaries to run.

#include "defines.h"
#include <stdint.h>
#include <math.h>
#ifdef HAVE_POWF
float powf(float x, float y);	// FreeBSD 3.X no longer defines this
#else
#define powf(x,y) (float)pow((double)x, (double)y)
#endif

// Biggest float
#define XUL	170141163178059628080016879768632819712.0

// PDP-11 floating point format
typedef struct {
  unsigned frac1:7;		// Fractional part of number
  unsigned exp:8;		// Excess 128 notation: -128 to +127
  unsigned sign:1;		// If 1, float is negative
  unsigned frac2:16;		// Fractional part of number
} pdpfloat;

// Internal variables
double fregs[8];		// Yes, there are only 6, it makes it easier
int FPC = 0;			// Status flags
int FPZ = 0;
int FPN = 0;
int FPV = 0;
int FPMODE = 0;			// 0 = float, 1 = doubles
int INTMODE = 0;		// 0 = integers, 1 = longs

// Temporary variables
double Srcflt;			// Float specified by FSRC field
pdpfloat *fladdr;		// Address of float  in dspace
int FP_AC;			// Accumulator field in ir
int32_t srclong;		// Longword from source address
int32_t dstlong;		// Longword for destination address
static char *buf, *buf2;	// for copylong

// Convert from PDP-11 float representation to native representation
void from11float(double * out, pdpfloat * in) {
  u_int16_t *wptr;
  wptr = (u_int16_t *) in;
  uint32_t *ptr;		// Will point at the IEE754 in value
  int sign;			// 1 bit wide
  int exp;			// 11 bits wide
  uint64_t frac;		// 52 bits wide

  // If input represents 0.0, send that back now
  if (FPMODE == 1) {
    if (in->sign == 0 && in->exp == 0 && in->frac2 == 0 &&
	in->frac1 == 0 && wptr[2] == 0 && wptr[3] == 0)
      { *out= 0.0; return; }
  } else {
    if (in->sign == 0 && in->exp == 0 && in->frac2 == 0 && in->frac1 == 0)
      { *out= 0.0; return; }
  }

  // Extract the sign, exponent and fraction from the PDP-11
  // format and make into IEE 754 format
  ptr = (uint32_t *) out;
  sign= in->sign;
  exp= in->exp + 894;			// 894 is 1023 - 129
  frac= ((uint64_t)in->frac1 << 45) | ((uint64_t)in->frac2 << 29);
  if (FPMODE == 1) {
    frac |= wptr[2] << 13;
    frac |= wptr[3] >> 3;
  }
  ptr[1]= (sign << 31) | (exp << 20) | (frac >> 32);
  ptr[0]= frac & 0xffffffff;

#if 0
  if (FPMODE == 1)
    FpDebug((dbg_file, "0%06o: double %06o;%06o;%06o;%06o -> %f\n",
	     regs[7], wptr[0], wptr[1], wptr[2], wptr[3], *out));
  else
    FpDebug((dbg_file, "0%06o: float %06o;%06o -> %f\n",
	     regs[7], wptr[0], wptr[1], *out));
#endif
}

// Convert from native representation to PDP-11 float representation
void to11float(double * in, pdpfloat * out) {
  uint32_t *ptr;		// Will point at the IEE754 in value
  int sign;			// 1 bit wide
  int exp;			// 11 bits wide
  uint64_t frac;		// 52 bits wide
  u_int16_t *wptr;		// Used for debugging

  // Debug: print out the native double value
  wptr = (u_int16_t *) out;
#if 0
  FpDebug((dbg_file, "0%06o %f -> ", regs[7], *in));
#endif

  // Input is zero, set all output bits zero
  if (*in == 0.0) {
    out->sign = 0;
    out->exp = 0;
    out->frac1 = 0;
    out->frac2 = 0;
    if (FPMODE == 1) {
      wptr[2] = 0;
      wptr[3] = 0;
#if 0
      FpDebug((dbg_file, "double 0;0;0;0\n"));
#endif
    } else
      FpDebug((dbg_file, "float 0;0\n"));
    return;
  }

  // Get the sign, exponent and fraction from the IEEE 754 double
  ptr = (uint32_t *) in;
  sign = ptr[1] >> 31;
  exp = (ptr[1] >> 20) & 0x7ff;
  frac = (((uint64_t) ptr[1] & 0xfffff) << 32) + ptr[0];

  // Convert to PDP-11 floating point format
  if (FPMODE == 1) {
    wptr[3] = (frac << 3) & 0xffff;
    wptr[2] = (frac >> 13) & 0xffff;
  }

  out->sign = sign;
  out->exp = (exp - 894) & 0xff;	// 894 is 1023 - 129
  out->frac2 = (frac >> 29) & 0xffff;
  out->frac1 = (frac >> 45) & 0x7f;

#if 0
  // Debug: print out the PDP-11 float value as words
  if (FPMODE == 1) {
    FpDebug((dbg_file, "double %06o;%06o;%06o;%06o\n",
	     wptr[0], wptr[1], wptr[2], wptr[3]));
  } else
    FpDebug((dbg_file, "float %06o;%06o\n", wptr[0], wptr[1]));
#endif
}

static struct {
  u_int16_t lo;
  u_int16_t hi;
} intpair;

// Load (and convert if necessary) the float
// described by the source address into Srcflt.
static void load_flt(void) {
  u_int16_t indirect, addr;
  u_int16_t *intptr;

  // FpDebug((dbg_file, "load_flt mode %d\n", DST_MODE));
  switch (DST_MODE) {
  case 0:
    Srcflt = fregs[DST_REG];
    fladdr = NULL;
    return;
  case 1:
    if (DST_REG == PC) {
      intptr = (u_int16_t *) & ispace[regs[DST_REG]];
      intpair.lo = *intptr;
      intpair.hi = 0;
      fladdr = (pdpfloat *) & intpair;
    } else
      fladdr = (pdpfloat *) & dspace[regs[DST_REG]];
    from11float(&Srcflt, fladdr);
    return;
  case 2:
    if (DST_REG == PC) {
      intptr = (u_int16_t *) & ispace[regs[DST_REG]];
      intpair.lo = *intptr;
      intpair.hi = 0;
      fladdr = (pdpfloat *) & intpair;
      from11float(&Srcflt, fladdr);
      regs[DST_REG] += 2;
    } else {
      fladdr = (pdpfloat *) & dspace[regs[DST_REG]];
      from11float(&Srcflt, fladdr);
      if (FPMODE)
	regs[DST_REG] += 8;
      else
	regs[DST_REG] += 4;
    }
    return;
  case 3:
    ll_word(regs[DST_REG], indirect);
    if (DST_REG == PC) {
      intptr = (u_int16_t *) & ispace[indirect];
      intpair.lo = *intptr;
      intpair.hi = 0;
      fladdr = (pdpfloat *) & intpair;
      from11float(&Srcflt, fladdr);
      regs[DST_REG] += 2;
    } else {
      fladdr = (pdpfloat *) & dspace[indirect];
      from11float(&Srcflt, fladdr);
      if (FPMODE)
	regs[DST_REG] += 8;
      else
	regs[DST_REG] += 4;
    }
    return;
  case 4:
    if (FPMODE)
      regs[DST_REG] -= 8;
    else
      regs[DST_REG] -= 4;
    fladdr = (pdpfloat *) & dspace[regs[DST_REG]];
    from11float(&Srcflt, fladdr);
    return;
  case 5:
    if (FPMODE)
      regs[DST_REG] -= 8;
    else
      regs[DST_REG] -= 4;
    ll_word(regs[DST_REG], indirect);
    fladdr = (pdpfloat *) & dspace[indirect];
    from11float(&Srcflt, fladdr);
    return;
  case 6:
    lli_word(regs[PC], indirect);
    regs[PC] += 2;
    indirect = regs[DST_REG] + indirect;
    fladdr = (pdpfloat *) & dspace[indirect];
    from11float(&Srcflt, fladdr);
    return;
  case 7:
    lli_word(regs[PC], indirect);
    regs[PC] += 2;
    indirect = regs[DST_REG] + indirect;
    ll_word(indirect, addr);
    fladdr = (pdpfloat *) & dspace[addr];
    from11float(&Srcflt, fladdr);
    return;
  }
  illegal();
}

// Save (and convert if necessary) Srcflt into
// the float described by the destination address
static void save_flt(void) {
  u_int16_t indirect;
  u_int16_t addr;
  pdpfloat *fladdr;

  // FpDebug((dbg_file, "save_flt mode %d\n", DST_MODE));
  switch (DST_MODE) {
  case 0:
    fregs[DST_REG] = Srcflt;
    return;
  case 1:
    fladdr = (pdpfloat *) & dspace[regs[DST_REG]];
    to11float(&Srcflt, fladdr);
    return;
  case 2:
    fladdr = (pdpfloat *) & dspace[regs[DST_REG]];
    to11float(&Srcflt, fladdr);
    if (DST_REG == PC)
      regs[DST_REG] += 2;
    else if (FPMODE)
      regs[DST_REG] += 8;
    else
      regs[DST_REG] += 4;
    return;
  case 3:
    ll_word(regs[DST_REG], indirect);
    fladdr = (pdpfloat *) & dspace[indirect];
    to11float(&Srcflt, fladdr);
    if (DST_REG == PC)
      regs[DST_REG] += 2;
    else if (FPMODE)
      regs[DST_REG] += 8;
    else
      regs[DST_REG] += 4;
    return;
  case 4:
    if (FPMODE)
      regs[DST_REG] -= 8;
    else
      regs[DST_REG] -= 4;
    fladdr = (pdpfloat *) & dspace[regs[DST_REG]];
    to11float(&Srcflt, fladdr);
    return;
  case 5:
    if (FPMODE)
      regs[DST_REG] -= 8;
    else
      regs[DST_REG] -= 4;
    ll_word(regs[DST_REG], indirect);
    fladdr = (pdpfloat *) & dspace[indirect];
    to11float(&Srcflt, fladdr);
    return;
  case 6:
    lli_word(regs[PC], indirect);
    regs[PC] += 2;
    indirect = regs[DST_REG] + indirect;
    fladdr = (pdpfloat *) & dspace[indirect];
    to11float(&Srcflt, fladdr);
    return;
  case 7:
    lli_word(regs[PC], indirect);
    regs[PC] += 2;
    indirect = regs[DST_REG] + indirect;
    ll_word(indirect, addr);
    fladdr = (pdpfloat *) & dspace[addr];
    to11float(&Srcflt, fladdr);
    return;
  }
  illegal();
}

// lli_long() - Load a long from the given ispace logical address.
#define lli_long(addr, word) \
	{ adptr= (u_int16_t *)&(ispace[addr]); copylong(word, *adptr); } \

// ll_long() - Load a long from the given logical address.
#define ll_long(addr, word) \
	{ adptr= (u_int16_t *)&(dspace[addr]); copylong(word, *adptr); } \

// sl_long() - Store a long from the given logical address.
#define sl_long(addr, word) \
	{ adptr= (u_int16_t *)&(dspace[addr]); copylong(*adptr, word); } \

static void load_long(void) {
  u_int16_t addr, indirect;

  switch (DST_MODE) {
  case 0:
    srclong = regs[DST_REG];
    return;
  case 1:
    addr = regs[DST_REG];
    if (DST_REG == PC) {
      lli_long(addr, srclong)
    } else {
      ll_long(addr, srclong);
    }
    return;
  case 2:
    addr = regs[DST_REG];
    if (DST_REG == PC) {
      lli_long(addr, srclong)
    } else {
      ll_long(addr, srclong);
    }
    regs[DST_REG] += 4;
    return;
  case 3:
    indirect = regs[DST_REG];
    if (DST_REG == PC) {
      lli_word(indirect, addr)
    } else {
      ll_word(indirect, addr);
    }
    regs[DST_REG] += 4;
    ll_long(addr, srclong);
    return;
  case 4:
    regs[DST_REG] -= 4;
    addr = regs[DST_REG];
    ll_long(addr, srclong);
    return;
  case 5:
    regs[DST_REG] -= 4;
    indirect = regs[DST_REG];
    ll_word(indirect, addr);
    ll_long(addr, srclong);
    return;
  case 6:
    lli_word(regs[PC], indirect);
    regs[PC] += 2;
    addr = regs[DST_REG] + indirect;
    ll_long(addr, srclong);
    return;
  case 7:
    lli_word(regs[PC], indirect);
    regs[PC] += 2;
    indirect = regs[DST_REG] + indirect;
    ll_word(indirect, addr);
    ll_long(addr, srclong);
    return;
  }
  illegal();
}

static void store_long(void) {
  u_int16_t addr, indirect;

  switch (DST_MODE) {
  case 0:
    regs[DST_REG] = dstlong;
    return;
  case 1:
    addr = regs[DST_REG];
    sl_long(addr, dstlong)
      return;
  case 2:
    addr = regs[DST_REG];
    sl_long(addr, dstlong)
      regs[DST_REG] += 4;
    return;
  case 3:
    indirect = regs[DST_REG];
    ll_word(indirect, addr);
    regs[DST_REG] += 4;
    sl_long(addr, dstlong);
    return;
  case 4:
    regs[DST_REG] -= 4;
    addr = regs[DST_REG];
    sl_long(addr, dstlong);
    return;
  case 5:
    regs[DST_REG] -= 4;
    indirect = regs[DST_REG];
    ll_word(indirect, addr);
    sl_long(addr, dstlong);
    return;
  case 6:
    lli_word(regs[PC], indirect);
    regs[PC] += 2;
    addr = regs[DST_REG] + indirect;
    sl_long(addr, dstlong);
    return;
  case 7:
    lli_word(regs[PC], indirect);
    regs[PC] += 2;
    indirect = regs[DST_REG] + indirect;
    ll_word(indirect, addr);
    sl_long(addr, dstlong);
    return;
  }
  illegal();
}

// Instruction handlers
void fpset() {
  switch (ir) {
  case 0170000:		// CFCC
    CC_C = FPC;
    CC_V = FPV;
    CC_Z = FPZ;
    CC_N = FPN;
    return;
  case 0170001:		// SETF
    FPMODE = 0;
    return;
  case 0170002:		// SETI
    INTMODE = 0;
    return;
  case 0170011:		// SETD
    FPMODE = 1;
    return;
  case 0170012:		// SETL
    INTMODE = 1;
    return;
  default:
    not_impl();
  }
}

void ldf() {
  // Load float
  FP_AC = (ir >> 6) & 3;
  load_flt();
  fregs[FP_AC] = Srcflt;
  FpDebug((dbg_file, "0%06o: ldf %f\n", regs[7], fregs[FP_AC]));
  FPC = 0;
  FPV = 0;
  if (fregs[FP_AC] == 0.0)
    FPZ = 1;
  else
    FPZ = 0;
  if (fregs[FP_AC] < 0.0)
    FPN = 1;
  else
    FPN = 0;
  FpDebug((dbg_file, "         ldf NZCV %d%d%d%d\n", FPN, FPZ, FPC, FPV));
}

void stf() {
  // Store float
  FP_AC = (ir >> 6) & 3;
  Srcflt = fregs[FP_AC];
  FpDebug((dbg_file, "0%06o: stf %f\n", regs[7], fregs[FP_AC]));
  save_flt();
}

void clrf() {
  // Store float
  FP_AC = (ir >> 6) & 3;
  FpDebug((dbg_file, "0%06o: clrf\n", regs[7]));
  Srcflt = 0.0;
  save_flt();
  FPC = FPZ = FPV = 0;
  FPZ = 1;
  FpDebug((dbg_file, "         clrf NZCV %d%d%d%d\n", FPN, FPZ, FPC, FPV));
}

void addf() {
  // Add float
  FP_AC = (ir >> 6) & 3;
  load_flt();
  FpDebug((dbg_file, "0%06o: addf %f %f ->", regs[7], fregs[FP_AC], Srcflt));
  fregs[FP_AC] += Srcflt;
  FpDebug((dbg_file, "%f\n", fregs[FP_AC]));
  FPC = 0;
  if (fregs[FP_AC] > XUL)
    FPV = 1;
  else
    FPV = 0;
  if (fregs[FP_AC] == 0.0)
    FPZ = 1;
  else
    FPZ = 0;
  if (fregs[FP_AC] < 0.0)
    FPN = 1;
  else
    FPN = 0;
  FpDebug((dbg_file, "         addf NZCV %d%d%d%d\n", FPN, FPZ, FPC, FPV));
}

void subf() {
  // Subtract float
  FP_AC = (ir >> 6) & 3;
  load_flt();
  FpDebug((dbg_file, "0%06o: subf %f %f ->", regs[7], fregs[FP_AC], Srcflt));
  fregs[FP_AC] -= Srcflt;
  FpDebug((dbg_file, "%f\n", fregs[FP_AC]));
  FPC = 0;
  if (fregs[FP_AC] > XUL)
    FPV = 1;
  else
    FPV = 0;
  if (fregs[FP_AC] == 0.0)
    FPZ = 1;
  else
    FPZ = 0;
  if (fregs[FP_AC] < 0.0)
    FPN = 1;
  else
    FPN = 0;
  FpDebug((dbg_file, "         subf NZCV %d%d%d%d\n", FPN, FPZ, FPC, FPV));
}

void negf() {
  // Negate float
  load_flt();
  FpDebug((dbg_file, "0%06o: negf %f\n", regs[7], Srcflt));
  Srcflt= -Srcflt;
  FPC = 0;
  FPV = 0;
  if (Srcflt == 0.0)
    FPZ = 1;
  else
    FPZ = 0;
  if (Srcflt < 0.0)
    FPN = 1;
  else
    FPN = 0;
  FpDebug((dbg_file, "         negf NZCV %d%d%d%d\n", FPN, FPZ, FPC, FPV));
}

void absf() {
  // Absolute float
  load_flt();
  FpDebug((dbg_file, "0%06o: absf %f\n", regs[7], Srcflt));
  if (Srcflt < 0.0)
    Srcflt= -Srcflt;
  FPC = 0;
  FPV = 0;
  FPN = 0;
  if (Srcflt == 0.0)
    FPZ = 1;
  else
    FPZ = 0;
  FpDebug((dbg_file, "         absf NZCV %d%d%d%d\n", FPN, FPZ, FPC, FPV));
}

void mulf() {
  // Multiply float
  FP_AC = (ir >> 6) & 3;
  load_flt();
  FpDebug((dbg_file, "0%06o: mulf %f %f -> ", regs[7], fregs[FP_AC], Srcflt));
  fregs[FP_AC] *= Srcflt;
  FpDebug((dbg_file, "%f\n", fregs[FP_AC]));
  FPC = 0;
  if (fregs[FP_AC] > XUL)
    FPV = 1;
  else
    FPV = 0;
  if (fregs[FP_AC] == 0.0)
    FPZ = 1;
  else
    FPZ = 0;
  if (fregs[FP_AC] < 0.0)
    FPN = 1;
  else
    FPN = 0;
  FpDebug((dbg_file, "         mulf NZCV %d%d%d%d\n", FPN, FPZ, FPC, FPV));
}

void moddf() {
  // Multiply and integerise float
  double x, y;

  FP_AC = (ir >> 6) & 3;
  load_flt();
  fregs[FP_AC] *= Srcflt;
  FpDebug((dbg_file, "0%06o: moddf %f %f ->", regs[7], fregs[FP_AC], Srcflt));
  y = fregs[FP_AC];
  if (y > 0.0)
    x = (double) floor((double) y);
  else
    x = (double) ceil((double) y);
  fregs[FP_AC | 1] = x;

  y = y - x;
  fregs[FP_AC] = y;
  FpDebug((dbg_file, "%f\n", fregs[FP_AC]));

  FPC = 0;
  if (fregs[FP_AC] > XUL)
    FPV = 1;
  else
    FPV = 0;
  if (fregs[FP_AC] == 0.0)
    FPZ = 1;
  else
    FPZ = 0;
  if (fregs[FP_AC] < 0.0)
    FPN = 1;
  else
    FPN = 0;
  FpDebug((dbg_file, "         moddf NZCV %d%d%d%d\n", FPN, FPZ, FPC, FPV));
}

void divf() {
  // Divide float
  FP_AC = (ir >> 6) & 3;
  load_flt();
  FpDebug((dbg_file, "0%06o: divf %f %f ->", regs[7], fregs[FP_AC], Srcflt));
  fregs[FP_AC] /= Srcflt;
  FpDebug((dbg_file, "%f\n", fregs[FP_AC]));
  FPC = 0;
  if (fregs[FP_AC] > XUL)
    FPV = 1;
  else
    FPV = 0;
  if (fregs[FP_AC] == 0.0)
    FPZ = 1;
  else
    FPZ = 0;
  if (fregs[FP_AC] < 0.0)
    FPN = 1;
  else
    FPN = 0;
  FpDebug((dbg_file, "         divf NZCV %d%d%d%d\n", FPN, FPZ, FPC, FPV));
}

void cmpf() {
  // Compare float
  FP_AC = (ir >> 6) & 3;
  load_flt();
  FpDebug((dbg_file, "0%06o: cmpf %f %f\n", regs[7], fregs[FP_AC], Srcflt));
  FPC = 0;
  FPV = 0;
  if (fregs[FP_AC] > Srcflt)
    FPN = 1;
  else
    FPN = 0;
  if (fregs[FP_AC] == Srcflt)
    FPZ = 1;
  else
    FPZ = 0;
  FpDebug((dbg_file, "         cmpf NZCV %d%d%d%d\n", FPN, FPZ, FPC, FPV));
}

void tstf() {
  // Test float
  FP_AC = (ir >> 6) & 3;
  load_flt();
  FPC = 0;
  FPV = 0;
  if (Srcflt < 0.0)
    FPN = 1;
  else
    FPN = 0;
  if (Srcflt == 0.0)
    FPZ = 1;
  else
    FPZ = 0;
  FpDebug((dbg_file, "0%06o: tstf NZCV %d%d%d%d\n", regs[7], FPN, FPZ, FPC, FPV));
}

void ldfps() {
  // Load FPP status
  load_dst();
  FpDebug((dbg_file, "0%06o: ldfps dstword 0x%x\n", regs[7], dstword));
  if (dstword & CC_NBIT)
    CC_N = 1;
  if (dstword & CC_ZBIT)
    CC_Z = 1;
  if (dstword & CC_VBIT)
    CC_V = 1;
  if (dstword & CC_CBIT)
    CC_C = 1;
}

void stfps() {
  // Store FPP status
  dstword = 0;
  if (CC_N)
    dstword |= CC_NBIT;
  if (CC_Z)
    dstword |= CC_ZBIT;
  if (CC_V)
    dstword |= CC_VBIT;
  if (CC_C)
    dstword |= CC_CBIT;
  FpDebug((dbg_file, "0%06o: stfps dstword 0x%x\n", regs[7], dstword));
  store_dst();
}

void lcdif() {
  // Convert int to float
  FP_AC = (ir >> 6) & 3;
  if (INTMODE == 0) {		// ints
    load_dst();
    fregs[FP_AC] = (float) dstword;
    FpDebug((dbg_file, "0%06o: ldcif int16 %d -> %f\n", regs[7], dstword, fregs[FP_AC]));
  } else {
    load_long();
    fregs[FP_AC] = (float) srclong;
    FpDebug((dbg_file, "0%06o: ldclf int32 %d -> %f\n", regs[7], srclong, fregs[FP_AC]));
  }
}

void stcfi() {
  // Convert int to float
  FP_AC = (ir >> 6) & 3;
  if (INTMODE == 0) {		// ints
    FpDebug((dbg_file, "0%06o: stcfi int16 %f\n", regs[7], fregs[FP_AC]));
    dstword = (int16_t) fregs[FP_AC];
    store_dst();
  } else {
    FpDebug((dbg_file, "0%06o: stcfi int32 %f\n", regs[7], fregs[FP_AC]));
    dstlong = (int32_t) fregs[FP_AC];
    store_long();
  }
}

void stexp() {
  // Store exponent
  pdpfloat pdptmp;
  FpDebug((dbg_file, "0%06o: stexp %f\n", regs[7], pdptmp));

  FP_AC = (ir >> 6) & 3;
  to11float(&fregs[FP_AC], &pdptmp);
  dstword = pdptmp.exp - 128;
  store_dst();
}

void stcdf() {
  FpDebug((dbg_file, "0%06o: stccf\n", regs[7]));
  // Switch FPMODE just while we're saving
  FPMODE = 1 - FPMODE;
  stf();
  FPMODE = 1 - FPMODE;
}

void ldcdf() {
  FpDebug((dbg_file, "0%06o: ldcdf\n", regs[7]));
  ldf();
}

void stst() {
  // For now
  FpDebug((dbg_file, "0%06o: stst null for now\n", regs[7]));
}

void ldexpp() {
  pdpfloat pdptmp;

  FP_AC = (ir >> 6) & 3;
  FpDebug((dbg_file, "ldexpp %f -> ", pdptmp));
  to11float(&fregs[FP_AC], &pdptmp);
  load_dst();			// dstword now holds new exponent
  dstword += 128;		// Convert to required exponent
  dstword &= 0xff;
  pdptmp.exp = dstword;
  from11float(&fregs[FP_AC], &pdptmp);
  FpDebug((dbg_file, "0%06o: %f\n", regs[7], pdptmp));
}
