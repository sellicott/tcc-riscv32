/* riscv_utils.h
 * Some helper functions and macros that make generating instructions easier
 * Implementations of the base instruction types, and macros for each 
 * instruction to generate the correct opcode from the memeonic.
 */

void emit_R(uint32_t funct7, uint32_t rs2, uint32_t rs1,
            uint32_t funct3, uint32_t rd, uint32_t opcode);

void emit_I(uint32_t imm, uint32_t rs1,
            uint32_t func3, uint32_t rd, uint32_t opcode);

void emit_S(uint32_t imm, uint32_t rs2, uint32_t rs1,
            uint32_t funct3, uint32_t opcode);

void emit_B(uint32_t imm, uint32_t rs2, uint32_t rs1,
            uint32_t funct3, uint32_t opcode);

void emit_U(uint32_t imm, uint32_t rd, uint32_t opcode);

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
#define emit_LBW(rd, rs1, imm)      (emit_I(imm, rs1, 0x4, rd,  0x03))
#define emit_LHW(rd, rs1, imm)      (emit_I(imm, rs1, 0x5, rd,  0x03))
#define emit_SB(rs1, rs2, imm)      (emit_S(imm, rs2, rs1, 0x0, 0x23))
#define emit_SH(rs1, rs2, imm)      (emit_S(imm, rs2, rs1, 0x1, 0x23))
#define emit_SW(rs1, rs2, imm)      (emit_S(imm, rs2, rs1, 0x2, 0x23))
#define emit_ADDI(rd, rs1, imm)     (emit_I(imm, rs1, 0x0, rd,  0x13))
#define emit_SLTI(rd, rs1, imm)     (emit_I(imm, rs1, 0x2, rd,  0x13))
#define emit_SLTIU(rd, rs1, imm)    (emit_I(imm, rs1, 0x3, rd,  0x13))
#define emit_XORI(rd, rs1, imm)     (emit_I(imm, rs1, 0x4, rd,  0x13))
#define emit_ORI(rd, rs1, imm)      (emit_I(imm, rs1, 0x6, rd,  0x13))
#define emit_ANDI(rd, rs1, imm)     (emit_I(imm, rs1, 0x7, rd,  0x13))
#define emit_SLLI(rd, rs1, shamt)   (emit_R(0x00, shamt, rs1, 0x1, rd, 0x13)
#define emit_SRLI(rd, rs1, shamt)   (emit_R(0x00, shamt, rs1, 0x5, rd, 0x13)
#define emit_SRAI(rd, rs1, shamt)   (emit_R(0x20, shamt, rs1, 0x5, rd, 0x13)
#define emit_ADD(rd, rs1, rs2)      (emit_R(0x00, rs2,   rs1, 0x0, rd, 0x33)
#define emit_SUB(rd, rs1, rs2)      (emit_R(0x20, rs2,   rs1, 0x0, rd, 0x33)
#define emit_SLL(rd, rs1, rs2)      (emit_R(0x00, rs2,   rs1, 0x1, rd, 0x33)
#define emit_SLT(rd, rs1, rs2)      (emit_R(0x00, rs2,   rs1, 0x2, rd, 0x33)
#define emit_SLTU(rd, rs1, rs2)     (emit_R(0x00, rs2,   rs1, 0x3, rd, 0x33)
#define emit_XOR(rd, rs1, rs2)      (emit_R(0x00, rs2,   rs1, 0x4, rd, 0x33)
#define emit_SRL(rd, rs1, rs2)      (emit_R(0x00, rs2,   rs1, 0x5, rd, 0x33)
#define emit_SRA(rd, rs1, rs2)      (emit_R(0x20, rs2,   rs1, 0x5, rd, 0x33)
#define emit_OR(rd, rs1, rs2)       (emit_R(0x00, rs2,   rs1, 0x6, rd, 0x33)
#define emit_AND(rd, rs1, rs2)      (emit_R(0x00, rs2,   rs1, 0x7, rd, 0x33)