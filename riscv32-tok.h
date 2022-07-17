/* ------------------------------------------------------------------ */
/* WARNING: relative order of tokens is important.                    */

// See https://riscv.org/wp-content/uploads/2017/05/riscv-spec-v2.2.pdf

/* registers */

/* register macros */

 DEF_ASM(zero)  // x0
 DEF_ASM(ra)    // x1
 DEF_ASM(sp)    // x2
 DEF_ASM(gp)    // x3
 DEF_ASM(tp)    // x4
 DEF_ASM(t0)    // x5
 DEF_ASM(t1)    // x6
 DEF_ASM(t2)    // x7
 DEF_ASM(s0)    // x8 - also fp
 DEF_ASM(s1)    // x9
 DEF_ASM(a0)    // x10
 DEF_ASM(a1)    // x11
 DEF_ASM(a2)    // x12
 DEF_ASM(a3)    // x13
 DEF_ASM(a4)    // x14
 DEF_ASM(a5)    // x15
 DEF_ASM(a6)    // x16
 DEF_ASM(a7)    // x17
 DEF_ASM(s2)    // x18
 DEF_ASM(s3)    // x19
 DEF_ASM(s4)    // x20
 DEF_ASM(s5)    // x21
 DEF_ASM(s6)    // x22
 DEF_ASM(s7)    // x23
 DEF_ASM(s8)    // x24
 DEF_ASM(s9)    // x25
 DEF_ASM(s10)   // x26
 DEF_ASM(s11)   // x27
 DEF_ASM(t3)    // x28
 DEF_ASM(t4)    // x29
 DEF_ASM(t5)    // x30
 DEF_ASM(t6)    // x31

 DEF_ASM(pc)

 DEF_ASM(fp)    // x8 / s0


 //DEF_ASM(s0) // = x8

#define DEF_ASM_WITH_SUFFIX(x, y) \
  DEF(TOK_ASM_ ## x ## _ ## y, #x #y)

/*   Loads */
 DEF_ASM(la)
 DEF_ASM(li)
 DEF_ASM(lb)
 DEF_ASM(lh)
 DEF_ASM(lw)
 DEF_ASM(lbu)
 DEF_ASM(lhu)

/* Stores */
 DEF_ASM(sb)
 DEF_ASM(sh)
 DEF_ASM(sw)

/* Shifts */
 DEF_ASM(sll)
 DEF_ASM(slli)
 DEF_ASM(srl)
 DEF_ASM(srli)
 DEF_ASM(sra)
 DEF_ASM(srai)

/* Arithmetic */
 DEF_ASM(add)
 DEF_ASM(addi)
 DEF_ASM(sub)
 DEF_ASM(lui)
 DEF_ASM(auipc)
 DEF_ASM(nop)

/* Logical */
 DEF_ASM(xor)
 DEF_ASM(xori)
 DEF_ASM(or)
 DEF_ASM(ori)
 DEF_ASM(and)
 DEF_ASM(andi)

/* Compare */
 DEF_ASM(slt)
 DEF_ASM(slti)
 DEF_ASM(sltu)
 DEF_ASM(sltiu)

/* Branch */
 DEF_ASM(beq)
 DEF_ASM(bne)
 DEF_ASM(blt)
 DEF_ASM(bge)
 DEF_ASM(bltu)
 DEF_ASM(bgeu)
 DEF_ASM(bgt)
 DEF_ASM(ble)
 DEF_ASM(bgtu)
 DEF_ASM(bleu)

/* Jump and Link */
 DEF_ASM(j)
 DEF_ASM(jal)
 DEF_ASM(jalr)
 DEF_ASM(jr)
 DEF_ASM(call)
 DEF_ASM(tail)
 DEF_ASM(ret)

/* Sync */
 DEF_ASM(fence)
 DEF_ASM_WITH_SUFFIX(fence, i)

/* System call */
 DEF_ASM(scall)
 DEF_ASM(sbreak)

/* Counters */
 DEF_ASM(rdcycle)
 DEF_ASM(rdcycleh)
 DEF_ASM(rdtime)
 DEF_ASM(rdtimeh)
 DEF_ASM(rdinstret)
 DEF_ASM(rdinstreth)

 /* control and status */
 DEF_ASM(csrrw)
 DEF_ASM(csrrs)
 DEF_ASM(csrrc)
 DEF_ASM(csrrwi)
 DEF_ASM(csrrsi)
 DEF_ASM(csrrci)

 /* control and status pseudoinstructions */
 DEF_ASM(csrr)
 DEF_ASM(csrw)
 DEF_ASM(csrs)
 DEF_ASM(csrc)
 DEF_ASM(csrwi)
 DEF_ASM(csrsi)
 DEF_ASM(csrci)

/* Privileged Instructions */
 DEF_ASM(ecall)
 DEF_ASM(ebreak)
 DEF_ASM(mrts)
 DEF_ASM(mrth)
 DEF_ASM(hrts)
 DEF_ASM(wfi)

 /* Multiply/Divide */
 DEF_ASM(mul)
 DEF_ASM(mulh)
 DEF_ASM(mulhsu)
 DEF_ASM(div)
 DEF_ASM(divu)
 DEF_ASM(rem)
 DEF_ASM(remu)

 /* two register pseudoinstructions */
 DEF_ASM(mv)
 DEF_ASM(seqz)
 DEF_ASM(snez)
 DEF_ASM(sltz)
 DEF_ASM(sgtz)


 /* immediate pseudoinstructions */
 DEF_ASM(beqz)
 DEF_ASM(bnez)
 DEF_ASM(blez)
 DEF_ASM(bgez)
 DEF_ASM(bltz)
 DEF_ASM(bgtz)