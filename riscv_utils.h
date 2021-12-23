#ifndef _RISCV_UTILS_H_
#define _RISCV_UTILS_H_

/* riscv_utils.h
 * Some helper functions and macros that make generating instructions easier
 * Implementations of the base instruction types, and macros for each 
 * instruction to generate the correct opcode from the memeonic.
 */


// Definitions for various instruction types: implemented in riscv32-asm.c

// Register instructions (math and stuff)
void emit_R(uint32_t funct7, uint32_t rs2, uint32_t rs1,
            uint32_t funct3, uint32_t rd, uint32_t opcode);

// immediate instructions
void emit_I(uint32_t imm, uint32_t rs1,
            uint32_t funct3, uint32_t rd, uint32_t opcode);

// store instructions
void emit_S(uint32_t imm, uint32_t rs2, uint32_t rs1,
            uint32_t funct3, uint32_t opcode);

// branch instructions
void emit_B(uint32_t imm, uint32_t rs2, uint32_t rs1,
            uint32_t funct3, uint32_t opcode);

// big immediate instructions (LUI and AUIPC)
void emit_U(uint32_t imm, uint32_t rd, uint32_t opcode);

// jump instructions
void emit_J(uint32_t imm, uint32_t rd, uint32_t opcode);


// Now for a big table of opcodes (RV32I) from p130 of ISA documentation
// https://github.com/riscv/riscv-isa-manual/releases/download/Ratified-IMAFDQC/riscv-spec-20191213.pdf
#define emit_LUI(rd, imm)           (emit_U(imm, rd,  0x37))
#define emit_AUIPC(rd, imm)         (emit_U(imm, rd,  0x17)) 
#define emit_JAL(rd, imm)           (emit_J(imm, rd,  0x6f))
#define emit_JALR(rd, rs1, imm)     (emit_I(imm, rs1, 0x0, rd,  0x67))
#define emit_BEQ(rs1, rs2, imm)     (emit_B(imm, rs2, rs1, 0x0, 0x63))
#define emit_BNE(rs1, rs2, imm)     (emit_B(imm, rs2, rs1, 0x1, 0x63))
#define emit_BLT(rs1, rs2, imm)     (emit_B(imm, rs2, rs1, 0x4, 0x63))
#define emit_BGE(rs1, rs2, imm)     (emit_B(imm, rs2, rs1, 0x5, 0x63))
#define emit_BLTU(rs1, rs2, imm)    (emit_B(imm, rs2, rs1, 0x6, 0x63))
#define emit_BGEU(rs1, rs2, imm)    (emit_B(imm, rs2, rs1, 0x7, 0x63))
#define emit_LB(rd, rs1, imm)       (emit_I(imm, rs1, 0x0, rd,  0x03))
#define emit_LH(rd, rs1, imm)       (emit_I(imm, rs1, 0x1, rd,  0x03))
#define emit_LW(rd, rs1, imm)       (emit_I(imm, rs1, 0x2, rd,  0x03))
#define emit_LBU(rd, rs1, imm)      (emit_I(imm, rs1, 0x4, rd,  0x03))
#define emit_LHU(rd, rs1, imm)      (emit_I(imm, rs1, 0x5, rd,  0x03))
#define emit_SB(rs1, rs2, imm)      (emit_S(imm, rs2, rs1, 0x0, 0x23))
#define emit_SH(rs1, rs2, imm)      (emit_S(imm, rs2, rs1, 0x1, 0x23))
#define emit_SW(rs1, rs2, imm)      (emit_S(imm, rs2, rs1, 0x2, 0x23))
#define emit_ADDI(rd, rs1, imm)     (emit_I(imm, rs1, 0x0, rd,  0x13))
#define emit_SLTI(rd, rs1, imm)     (emit_I(imm, rs1, 0x2, rd,  0x13))
#define emit_SLTIU(rd, rs1, imm)    (emit_I(imm, rs1, 0x3, rd,  0x13))
#define emit_XORI(rd, rs1, imm)     (emit_I(imm, rs1, 0x4, rd,  0x13))
#define emit_ORI(rd, rs1, imm)      (emit_I(imm, rs1, 0x6, rd,  0x13))
#define emit_ANDI(rd, rs1, imm)     (emit_I(imm, rs1, 0x7, rd,  0x13))
#define emit_SLLI(rd, rs1, shamt)   (emit_R(0x00, shamt, rs1, 0x1, rd, 0x13))
#define emit_SRLI(rd, rs1, shamt)   (emit_R(0x00, shamt, rs1, 0x5, rd, 0x13))
#define emit_SRAI(rd, rs1, shamt)   (emit_R(0x20, shamt, rs1, 0x5, rd, 0x13))
#define emit_ADD(rd, rs1, rs2)      (emit_R(0x00, rs2,   rs1, 0x0, rd, 0x33))
#define emit_SUB(rd, rs1, rs2)      (emit_R(0x20, rs2,   rs1, 0x0, rd, 0x33))
#define emit_SLL(rd, rs1, rs2)      (emit_R(0x00, rs2,   rs1, 0x1, rd, 0x33))
#define emit_SLT(rd, rs1, rs2)      (emit_R(0x00, rs2,   rs1, 0x2, rd, 0x33))
#define emit_SLTU(rd, rs1, rs2)     (emit_R(0x00, rs2,   rs1, 0x3, rd, 0x33))
#define emit_XOR(rd, rs1, rs2)      (emit_R(0x00, rs2,   rs1, 0x4, rd, 0x33))
#define emit_SRL(rd, rs1, rs2)      (emit_R(0x00, rs2,   rs1, 0x5, rd, 0x33))
#define emit_SRA(rd, rs1, rs2)      (emit_R(0x20, rs2,   rs1, 0x5, rd, 0x33))
#define emit_OR(rd, rs1, rs2)       (emit_R(0x00, rs2,   rs1, 0x6, rd, 0x33))
#define emit_AND(rd, rs1, rs2)      (emit_R(0x00, rs2,   rs1, 0x7, rd, 0x33))
// FM is 4 bits, pred is 4 bits, succ is 4 bits. rs1 and rd are reserved (set to 0)
#define emit_FENCE(succ, pred, fm) (emit_I( \
    (0xf & fm << 8) | (0xf & pred << 4) | ( 0xf & succ), 0x0, 0x0, 0x0, 0x0f) \
)
#define emit_ECALL()    (emit_I(0x000, 0x00, 0x0, 0x00, 0x73))
#define emit_EBREAK()   (emit_I(0x001, 0x00, 0x0, 0x00, 0x73))

// RV32M extension set
#define emit_MUL(rd, rs1, rs2)      (emit_R(0x01, rs2, rs1, 0x0, rd, 0x33))
#define emit_MULH(rd, rs1, rs2)     (emit_R(0x01, rs2, rs1, 0x1, rd, 0x33))
#define emit_MULHSU(rd, rs1, rs2)   (emit_R(0x01, rs2, rs1, 0x2, rd, 0x33))
#define emit_MULHU(rd, rs1, rs2)    (emit_R(0x01, rs2, rs1, 0x3, rd, 0x33))
#define emit_DIV(rd, rs1, rs2)      (emit_R(0x01, rs2, rs1, 0x4, rd, 0x33))
#define emit_DIVU(rd, rs1, rs2)     (emit_R(0x01, rs2, rs1, 0x5, rd, 0x33))
#define emit_REM(rd, rs1, rs2)      (emit_R(0x01, rs2, rs1, 0x6, rd, 0x33))
#define emit_REMU(rd, rs1, rs2)     (emit_R(0x01, rs2, rs1, 0x7, rd, 0x33))


// Pseudo instructions (from https://risc-v.guru/instructions/)

// note that this will not produce PIC code
#define emit_LA(rd, symbol) ( \
    emit_AUIPC(rd, symbol >> 12); \
    emit_ADDI(rd, rd, symbol))

#define emit_NOP() (emit_ADDI(0, 0, 0))

#define emit_LI(rd, imm)\
    emit_LUI(rd, imm >> 12); \
    emit_JALR(rd, rd, imm))

#define emit_MV(rd, rs)     (emit_ADDI(rd, rs, 0))
//#define emit_SEXT_W(rd, rs) (emit_ADDIW(rd, rs, 0))

// branches
#define emit_BEQZ(rs, offset)   (emit_BEQ(rs, 0, offset))
#define emit_BNEZ(rs, offset)   (emit_BNE(rs, 0, offset))
#define emit_BLEZ(rs, offset)   (emit_BGE(0, rs, offset))
#define emit_BGEZ(rs, offset)   (emit_BGE(rs, 0, offset))
#define emit_BLTZ(rs, offset)   (emit_BLT(rs, 0, offset))
#define emit_BGTZ(rs, offset)   (emit_BLT(0, rs, offset))
#define emit_BGT(rs, rt, offset)    (emit_BLT(rt, rs, offset))
#define emit_BGTU(rs, rt, offset)   (emit_BLTU(rt, rs, offset))
#define emit_BLEU(rs, rt, offset)   (emit_BGEU(rt, rs, offset))

// comparisons
#define emit_SEQZ(rd, rs)   (emit_SLTIU(rd, rs, 1))
#define emit_SNEZ(rd, rs)   (emit_SLTU(rd, 0, rs))
#define emit_SLTZ(rd, rs)   (emit_SLT(rd, rs, 0))
#define emit_SGTZ(rd, rs)   (emit_SLT(rd, 0, rs))

// counters
// TODO

// Jump and Link
#define emit_J_inst(offset)      (emit_JAL(0, offset))
#define emit_JAL_x1(offset) (emit_JAL(1, offset))
#define emit_JR(rs)         (emit_JALR(0, rs, 0))
#define emit_JALR_x1(rs)    (emit_JALR(1, rs, 0))
#define emit_RET()          (emit_JALR(0, 1, 0))

#define emit_CALL(offset) (\
    emit_AUIPC(6, offset >> 12); \
    emit_JALR(1, 6, offset))

#define emit_TAIL(offset) (\
    emit_AUIPC(6, offset >> 12); \
    emit_JALR(0, 6, offset))

// Logical
#define emit_NOT(rd, rs)    (emit_XORI(rd, rs, -1))
#define emit_NEG(rd, rs)    (emit_SUB(rd, 0, rs))
//#define emit_NEGW(rd, rs)   (emit_SUBW(rd, 0, rs))

// Sync
#define emit_FENCE_ALL()        (emit_FENCE(0xf, 0xf, 0x0))
#define emit_FENCE_DEFAULT()    (emit_FENCE(0x0, 0x0, 0x0))

#endif