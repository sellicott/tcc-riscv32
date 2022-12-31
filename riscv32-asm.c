/*************************************************************/
/*
 *  RISCV32 assembler for TCC
 *  Modified from riscv64 version
 *
 */

#ifdef SDE_RISCV32_DEV
#undef TARGET_DEFS_ONLY
#endif
#ifdef TARGET_DEFS_ONLY

#define CONFIG_TCC_ASM
#define NB_ASM_REGS 32

ST_FUNC void g( int c );
ST_FUNC void gen_le16( int c );
ST_FUNC void gen_le32( int c );

/*************************************************************/
#else
/*************************************************************/
#define USING_GLOBALS
#include "riscv_utils.h"
#include "tcc.h"

enum {
    OPT_REG,
    OPT_IM12S,
    OPT_IM21,
    OPT_IM32,
    OPT_SYM,
};
#define OP_REG ( 1 << OPT_REG )
#define OP_IM32 ( 1 << OPT_IM32 )
#define OP_IM21 ( 1 << OPT_IM21 )
#define OP_IM12S ( 1 << OPT_IM12S )
#define OP_SYM ( 1 << OPT_SYM )

// I don't think we need these anymore, but I haven't deleted them yet
#define ENCODE_RS1( register_index ) ( ( register_index ) << 15 )
#define ENCODE_RS2( register_index ) ( ( register_index ) << 20 )
#define ENCODE_RD( register_index ) ( ( register_index ) << 7 )


// --------------------------- boilerplate tcc requirements ----------------- //
ST_FUNC void g( int i )
{
    int ind1;
    if( nocode_wanted )
        return;
    ind1 = ind + 1;
    if( ind1 > cur_text_section->data_allocated )
        section_realloc( cur_text_section, ind1 );
    cur_text_section->data[ ind ] = i;
    ind = ind1;
}

ST_FUNC void gen_le16( int i )
{
    int ind1;
    if( nocode_wanted )
        return;
    ind1 = ind + 4;
    if( ind1 > cur_text_section->data_allocated )
        section_realloc( cur_text_section, ind1 );
    cur_text_section->data[ ind++ ] = i & 0xFF;
    cur_text_section->data[ ind++ ] = ( i >> 8 ) & 0xFF;
}

ST_FUNC void gen_le32( int i )
{
    int ind1;
    if( nocode_wanted )
        return;
    ind1 = ind + 4;
    if( ind1 > cur_text_section->data_allocated )
        section_realloc( cur_text_section, ind1 );
    cur_text_section->data[ ind++ ] = i & 0xFF;
    cur_text_section->data[ ind++ ] = ( i >> 8 ) & 0xFF;
    cur_text_section->data[ ind++ ] = ( i >> 16 ) & 0xFF;
    cur_text_section->data[ ind++ ] = ( i >> 24 ) & 0xFF;
}
ST_FUNC void gen_expr32( ExprValue *pe )
{
    gen_le32( pe->v );
}

// ---------------------- end boilerplate tcc requirements ----------------- //


typedef struct Operand {
    uint32_t type;
    union {
        uint8_t reg;
        uint16_t regset;
        ExprValue e;
    };
} Operand;


// return the type for a variable based on its size
static uint32_t imm_op_type_from_size( uint32_t value )
{
    uint32_t type = OP_IM32;
    // check if we are in a 12b signed range
    if( (int32_t)value >= -2048 && (int32_t)value < 2048 ) {
        type |= OP_IM12S;
    }
    // check if we are within a 21b range
    if( value <= 0x1fffff ) {
        type |= OP_IM21;
    }

    return type;
}

/* Parse a text containing operand and store the result in OP */
static void parse_operand( TCCState *s1, Operand *op )
{
    ExprValue e;
    int8_t reg;

    op->type = 0;

    if( ( reg = asm_parse_regvar( tok ) ) != -1 ) {
        next(); // skip register name
        op->type = OP_REG;
        op->reg = (uint8_t)reg;
        return;
    }
    else if( tok == '$' ) {
        /* constant value */
        next(); // skip '#' or '$'
    }
    asm_expr( s1, &e );
    op->type = OP_IM32;
    op->e = e;
    if( !op->e.sym ) {
        op->type = imm_op_type_from_size( op->e.v );
    }
    else {
        // Deal with the case of a symbol.
        // If we have a symbol we will let the linker handle it and just put in a zero for the
        // immediate value, we also need to put an entry into the reallocation table, this should
        // however, the entry will be different depending on the instruction, so ignore it for now.

        // get the type and value information from the included symbol
        Sym *sym = op->e.sym;
        op->type = OP_SYM;
        if( ( reg = asm_parse_regvar( sym->v ) ) != -1 ) {
            op->type |= OP_REG;
            op->reg = reg;
            return;
        }

        // immediate value? do type size checking
        op->type |= imm_op_type_from_size( sym->c );
        op->e.v = sym->c;
    }
}

// return false (0) if next operand not a register and true (1) if it is
static int check_register( const Operand *op )
{
    if( op->type != OP_REG ) {
        tcc_error_noabort( "expected a register" );
        return 0;
    }
    return 1;
}


// return false (0) if next operand not an immediate and true (1) if it is
static int check_immediate( const Operand *op )
{
    if( op->type != OP_IM12S && op->type != OP_IM32 && op->type != OP_IM21 ) {
        tcc_error_noabort( "expected an immediate" );
        return 0;
    }
    return 1;
}


// implement helper functions from riscv_utils.h
// Register instructions (math and stuff)
void emit_R(
    uint32_t funct7, uint32_t rs2, uint32_t rs1, uint32_t funct3, uint32_t rd, uint32_t opcode )
{
    const uint32_t instruction =
        ( funct7 << 25 ) | ( rs2 << 20 ) | ( rs1 << 15 ) | ( funct3 << 12 ) | ( rd << 7 ) | opcode;

    o( instruction );
}

// immediate instructions
void emit_I( uint32_t imm, uint32_t rs1, uint32_t funct3, uint32_t rd, uint32_t opcode )
{
    const uint32_t instruction =
        ( imm << 20 ) | ( rs1 << 15 ) | ( funct3 << 12 ) | ( rd << 7 ) | opcode;

    o( instruction );
}

// store instructions
void emit_S( uint32_t imm, uint32_t rs2, uint32_t rs1, uint32_t funct3, uint32_t opcode )
{
    // we have to break up the immediate value into two sections (11:5, 4:0)
    const uint32_t imm_h = 0x7f & ( imm >> 5 );
    const uint32_t imm_l = 0x1f & imm;
    const uint32_t instruction = ( imm_h << 25 ) | ( rs2 << 20 ) | ( rs1 << 15 ) |
                                 ( funct3 << 12 ) | ( imm_l << 7 ) | opcode;

    o( instruction );
}

/* branch instructions
 * takes a 13-bit immediate value (LSB is discarded)
 */
void emit_B( uint32_t imm, uint32_t rs2, uint32_t rs1, uint32_t funct3, uint32_t opcode )
{
    // we have to break up the immediate value into two sections (12,10:5, 4:1,11)
    // imm_h[5:0] = {12, 10:5}
    // imm_l[5:0] = {4:1, 11}
    const uint32_t imm_h = 0x7f & ( ( ( 0x800 & imm ) >> 1 ) | ( 0x7e0 & imm ) ) >> 5;
    const uint32_t imm_l = ( 0x1e & imm ) | ( 0x1 & ( imm >> 11 ) );
    const uint32_t instruction = ( imm_h << 25 ) | ( rs2 << 20 ) | ( rs1 << 15 ) |
                                 ( funct3 << 12 ) | ( imm_l << 7 ) | opcode;

    o( instruction );
}

/* big immediate instructions (LUI and AUIPC)
 * takes a 24-bit immediate value
 * we expect the immediate passed into this function to be in the lower space (i.e we will shift)
 */
void emit_U( uint32_t imm, uint32_t rd, uint32_t opcode )
{
    const uint32_t instruction = ( imm << 12 ) | ( rd << 7 ) | opcode;
    o( instruction );
}

/* jump instructions
 * takes a 21-bit immediate value
 */
void emit_J( uint32_t imm, uint32_t rd, uint32_t opcode )
{
    // immediate value 20|10:1|11|19:12
    // mask off bits 19:12 then shift them back
    // mask off bit 11 then shift it over to bit 20
    // mask off bits 10:1, then shift over 21
    // mask off bit 21, then shift over 31
    const uint32_t immediate = ( ( ( imm >> 12 ) & 0xff ) << 12 ) |
                               ( ( ( imm >> 11 ) & 1 ) << 20 ) |
                               ( ( ( imm >> 1 ) & 0x3ff ) << 21 ) | ( ( ( imm >> 20 ) & 1 ) << 31 );

    const uint32_t instruction = immediate | ( rd << 7 ) | opcode;
    o( instruction );
}

/*
 * Add an entry to the elf relocation table for the symbol in the operand op.
 * The type of the relocation table entry needs to match format of immediate value used by the
 * instruction.
 */
void generate_symbol_reallocation( const Operand *op, int type )
{
    if( op && op->e.sym ) {
        greloc( cur_text_section, op->e.sym, ind, type );
    }
}

// ------------------------- end basic helper functions --------------------- //

static void asm_nullary_opcode( TCCState *s1, int token )
{
    switch( token ) {
        case TOK_ASM_wfi:
            // I don't really know what WFI is
            o( ( 0x1C << 2 ) | 3 | ( 0x105 << 20 ) );
            return;

        case TOK_ASM_ret: emit_RET(); return;

        default: expect( "nullary instruction" );
    }
}

// Note: Those all map to CSR--so they are pseudo-instructions.
static void asm_unary_opcode( TCCState *s1, int token )
{
    Operand op;
    int rd;
    parse_operand( s1, &op );
    if( token != TOK_ASM_j && op.type != OP_REG ) {
        tcc_error( "'%s': Expected operand to be a register\n"
                   "received: %d",
            get_tok_str( token, NULL ), op.reg );
        return;
    }
    else if( token == TOK_ASM_j && op.type == OP_REG ) {
        tcc_error( "'%s': Expected operand to be an immediate offset\n"
                   "received: %ld",
            get_tok_str( token, NULL ), op.e.v );
        return;
    }

    rd = op.reg;

    switch( token ) {
        case TOK_ASM_j: emit_J_inst( op.e.v ); return;
        case TOK_ASM_rdcycle: emit_RDCYCLE( rd ); return;
        case TOK_ASM_rdcycleh: emit_RDCYCLEH( rd ); return;
        case TOK_ASM_rdtime: emit_RDTIME( rd ); return;
        case TOK_ASM_rdtimeh: emit_RDTIMEH( rd ); return;
        case TOK_ASM_rdinstret: emit_RDINSTRET( rd ); return;
        case TOK_ASM_rdinstreth: emit_RDINSTRETH( rd ); return;
        default: expect( "unary instruction" );
    }
}

static void asm_binary_pseudocode( TCCState *s1, int token )
{
    Operand rs, rd;
    parse_operand( s1, &rd );
    if( rd.type != OP_REG ) {
        tcc_error(
            "'%s': Expected destination operand that is a register", get_tok_str( token, NULL ) );
        return;
    }
    // printf("hi 1\n");
    if( tok == ',' ) {
        next();
    }
    else {
        expect( "','" );
    }
    // printf("hi 2\n");
    parse_operand( s1, &rs );
    if( rs.type != OP_REG ) {
        tcc_error( "'%s': Expected source operand that is a register", get_tok_str( token, NULL ) );
        return;
    }

    switch( token ) {
        case TOK_ASM_mv: emit_MV( rd.reg, rs.reg ); return;
        // comparison to zero pseudoinstructions
        case TOK_ASM_seqz: emit_SEQZ( rd.reg, rs.reg ); return;
        case TOK_ASM_snez: emit_SNEZ( rd.reg, rs.reg ); return;
        case TOK_ASM_sltz: emit_SLTZ( rd.reg, rs.reg ); return;
        case TOK_ASM_sgtz: emit_SGTZ( rd.reg, rs.reg ); return;
    }
}

static void asm_branch_zero_opcode( TCCState *s1, int token )
{

    // Branch (RS1,IMM); SB-format
    uint32_t offset = 0;
    Operand r1, imm;
    parse_operand( s1, &r1 );
    if( r1.type != OP_REG ) {
        tcc_error( "'%s': Expected first operand to be a register\n"
                   "received: %d",
            get_tok_str( token, NULL ), r1.reg );
        return;
    }
    if( tok == ',' )
        next();
    else
        expect( "','" );
    parse_operand( s1, &imm );

    offset = imm.e.v;
    if( offset > 0xfff ) {
        tcc_error( "'%s': Expected third operand that is an immediate value between 0 and 0xfff\n"
                   "received: %ld",
            get_tok_str( token, NULL ), imm.e.v );
        return;
    }
    if( offset & 1 ) {
        tcc_error( "'%s': Expected third operand that is an even immediate value",
            get_tok_str( token, NULL ) );
        return;
    }

    generate_symbol_reallocation( &imm, R_RISCV_BRANCH );

    switch( token ) {
        case TOK_ASM_beqz: emit_BEQZ( r1.reg, offset ); return;
        case TOK_ASM_bnez: emit_BNEZ( r1.reg, offset ); return;
        case TOK_ASM_blez: emit_BEQZ( r1.reg, offset ); return;
        case TOK_ASM_bgez: emit_BGEZ( r1.reg, offset ); return;
        case TOK_ASM_bltz: emit_BLTZ( r1.reg, offset ); return;
        case TOK_ASM_bgtz: emit_BGTZ( r1.reg, offset ); return;
        default: expect( "known branch instruction" );
    }
}

static void asm_binary_opcode( TCCState *s1, int token )
{
    Operand ops[ 2 ];
    uint32_t rd;
    uint32_t imm;
    int ind_bak;

    parse_operand( s1, &ops[ 0 ] );
    if( ops[ 0 ].type != OP_REG ) {
        tcc_error(
            "'%s': Expected destination operand that is a register", get_tok_str( token, NULL ) );
        return;
    }
    // printf("hi 1\n");
    if( tok == ',' ) {
        next();
    }
    else {
        expect( "','" );
    }
    // printf("hi 2\n");
    parse_operand( s1, &ops[ 1 ] );

    // la pseudoinstruction can load a full 32b word
    if( token != TOK_ASM_la ) {
        if( !( ops[ 1 ].type & OP_IM32 ) ) {
            tcc_error( "'%s': Expected second source operand that is an immediate value",
                get_tok_str( token, NULL ) );
            return;
        }
        else if( ops[ 1 ].e.v >= 0x100000 ) {
            tcc_error( "'%s': Expected second source operand that is an immediate value between 0 "
                       "and 0xfffff",
                get_tok_str( token, NULL ) );
            return;
        }
    }
    rd = ops[ 0 ].reg;
    imm = ops[ 1 ].e.v;

    switch( token ) {
        case TOK_ASM_la:
            // hacky method to generate relocation entries at the correct offsets (ind)
            ind_bak = ind;
            generate_symbol_reallocation( &ops[ 1 ], R_RISCV_HI20 );
            ind = ind + 4;
            generate_symbol_reallocation( &ops[ 1 ], R_RISCV_LO12_I );
            // rewind offset to put instructions at the correct offsets
            ind = ind_bak;
            emit_LA( rd, imm );
            return;
        case TOK_ASM_li:
            // hacky method to generate relocation entries at the correct offsets (ind)
            ind_bak = ind;
            generate_symbol_reallocation( &ops[ 1 ], R_RISCV_HI20 );
            ind = ind + 4;
            generate_symbol_reallocation( &ops[ 1 ], R_RISCV_LO12_I );
            // rewind offset to put instructions at the correct offsets
            ind = ind_bak;
            emit_LI( rd, imm );
            return;
        case TOK_ASM_lui:
            generate_symbol_reallocation( &ops[ 1 ], R_RISCV_HI20 );
            emit_LUI( rd, imm );
            return;
        case TOK_ASM_auipc:
            generate_symbol_reallocation( &ops[ 1 ], R_RISCV_HI20 );
            emit_AUIPC( rd, imm );
            return;
        default: expect( "binary instruction" );
    }
}

static void asm_branch_opcode( TCCState *s1, int token )
{
    uint32_t offset = 0;
    Operand ops[ 2 ], imm;
    parse_operand( s1, &ops[ 0 ] );
    if( ops[ 0 ].type != OP_REG ) {
        tcc_error( "'%s': Expected first operand to be a register\n"
                   "received: %d",
            get_tok_str( token, NULL ), ops[ 0 ].reg );
        return;
    }
    if( tok == ',' )
        next();
    else
        expect( "','" );
    parse_operand( s1, &ops[ 1 ] );
    if( ops[ 1 ].type != OP_REG ) {
        tcc_error( "'%s': Expected second operand to be a register\n"
                   "received: %d",
            get_tok_str( token, NULL ), ops[ 1 ].reg );
        return;
    }
    if( tok == ',' )
        next();
    else
        expect( "','" );
    parse_operand( s1, &imm );

    offset = imm.e.v;
    // if we are using a symbol, the value will be handled by the relocation table
    if( imm.type & OP_SYM ) {
        offset = 0;
    }
    if( offset > 0xfff ) {
        tcc_error( "'%s': Expected third operand that is an immediate value between 0 and 0xfff\n"
                   "received: %u",
            get_tok_str( token, NULL ), offset );
        return;
    }
    if( offset & 1 ) {
        tcc_error( "'%s': Expected third operand that is an even immediate value, received: %u",
            get_tok_str( token, NULL ), offset );
        return;
    }

    generate_symbol_reallocation( &imm, R_RISCV_BRANCH );

    switch( token ) {
        case TOK_ASM_beq: emit_BEQ( ops[ 0 ].reg, ops[ 1 ].reg, offset ); return;
        case TOK_ASM_bne: emit_BNE( ops[ 0 ].reg, ops[ 1 ].reg, offset ); return;
        case TOK_ASM_blt: emit_BLT( ops[ 0 ].reg, ops[ 1 ].reg, offset ); return;
        case TOK_ASM_ble: emit_BLE( ops[ 0 ].reg, ops[ 1 ].reg, offset ); return;

        case TOK_ASM_bltu: emit_BLTU( ops[ 0 ].reg, ops[ 1 ].reg, offset ); return;
        case TOK_ASM_bgeu: emit_BGEU( ops[ 0 ].reg, ops[ 1 ].reg, offset ); return;
        case TOK_ASM_bgtu: emit_BGTU( ops[ 0 ].reg, ops[ 1 ].reg, offset ); return;
        case TOK_ASM_bleu: emit_BLEU( ops[ 0 ].reg, ops[ 1 ].reg, offset ); return;

        default: expect( "known branch instruction" );
    }
}

// handle the register opcodes that don't have an immediate value (except for shifts)
static void asm_binary_register_opcode( TCCState *s1, int token )
{
    // start by getting the next three operands and check that they are all registers
    Operand rd, r1, r2;
    parse_operand( s1, &rd );
    if( !check_register( &rd ) ) {
        tcc_error( "'%s': Expected destination to be a register", get_tok_str( token, NULL ) );
    }

    if( tok == ',' ) {
        next();
    }
    else {
        expect( "','" );
    }
    parse_operand( s1, &r1 );
    if( !check_register( &r1 ) ) {
        tcc_error(
            "'%s': Expected first source operand to be a register", get_tok_str( token, NULL ) );
    }

    if( tok == ',' ) {
        next();
    }
    else {
        expect( "','" );
    }
    parse_operand( s1, &r2 );
    // check that we are using a register, or that we have an immediate between 0 and 31 (for
    // shifts)
    if( !( r2.type & OP_REG ) && r2.e.v > 31 ) {
        tcc_error(
            "'%s': Expected second source operand to be a register or immediate between 0 and 31",
            get_tok_str( token, NULL ) );
        return;
    }

    // switch through the various register instructions
    switch( token ) {
        case TOK_ASM_slli: emit_SLLI( rd.reg, r1.reg, r2.e.v ); return;
        case TOK_ASM_srli: emit_SRLI( rd.reg, r1.reg, r2.e.v ); return;
        case TOK_ASM_srai: emit_SRAI( rd.reg, r1.reg, r2.e.v ); return;
        case TOK_ASM_add: emit_ADD( rd.reg, r1.reg, r2.reg ); return;
        case TOK_ASM_sub: emit_SUB( rd.reg, r1.reg, r2.reg ); return;
        case TOK_ASM_sll: emit_SLL( rd.reg, r1.reg, r2.reg ); return;
        case TOK_ASM_slt: emit_SLT( rd.reg, r1.reg, r2.reg ); return;
        case TOK_ASM_sltu: emit_SLTU( rd.reg, r1.reg, r2.reg ); return;
        case TOK_ASM_xor: emit_XOR( rd.reg, r1.reg, r2.reg ); return;
        case TOK_ASM_srl: emit_SRL( rd.reg, r1.reg, r2.reg ); return;
        case TOK_ASM_sra: emit_SRA( rd.reg, r1.reg, r2.reg ); return;
        case TOK_ASM_or: emit_OR( rd.reg, r1.reg, r2.reg ); return;
        case TOK_ASM_and: emit_AND( rd.reg, r1.reg, r2.reg ); return;
        case TOK_ASM_mul: emit_MUL( rd.reg, r1.reg, r2.reg ); return;
        case TOK_ASM_mulh: emit_MULH( rd.reg, r1.reg, r2.reg ); return;
        case TOK_ASM_mulhsu: emit_MULHSU( rd.reg, r1.reg, r2.reg ); return;
        case TOK_ASM_div: emit_DIV( rd.reg, r1.reg, r2.reg ); return;
        case TOK_ASM_divu: emit_DIVU( rd.reg, r1.reg, r2.reg ); return;
        case TOK_ASM_rem: emit_REM( rd.reg, r1.reg, r2.reg ); return;
        case TOK_ASM_remu: emit_REMU( rd.reg, r1.reg, r2.reg ); return;
        default: expect( "register instruction" );
    }
}

static void asm_immediate_opcode( TCCState *s1, int token )
{
    // start by getting the next three operands and check that they are all registers
    Operand regs[ 2 ], imm;
    parse_operand( s1, &regs[ 0 ] );
    if( !check_register( &regs[ 0 ] ) ) {
        tcc_error( "'%s': Expected destination to be a register", get_tok_str( token, NULL ) );
        return;
    }

    if( tok == ',' ) {
        next();
    }
    else {
        expect( "','" );
    }
    parse_operand( s1, &regs[ 1 ] );
    if( !check_register( &regs[ 1 ] ) ) {
        tcc_error(
            "'%s': Expected second source operand to be a register", get_tok_str( token, NULL ) );
        return;
    }

    if( tok == ',' ) {
        next();
    }
    else {
        expect( "','" );
    }
    parse_operand( s1, &imm );
    // check that we have an 12bit immediate
    if( !( imm.type & OP_IM12S ) ) {
        tcc_error( "'%s': Expected third operand that is an immediate value between 0 and 0xfff",
            get_tok_str( token, NULL ) );
        return;
    }

    // switch through the various register instructions
    switch( token ) {
        case TOK_ASM_addi: emit_ADDI( regs[ 0 ].reg, regs[ 1 ].reg, imm.e.v ); return;
        case TOK_ASM_slti: emit_SLTI( regs[ 0 ].reg, regs[ 1 ].reg, imm.e.v ); return;
        case TOK_ASM_sltiu: emit_SLTIU( regs[ 0 ].reg, regs[ 1 ].reg, imm.e.v ); return;
        case TOK_ASM_xori: emit_XORI( regs[ 0 ].reg, regs[ 1 ].reg, imm.e.v ); return;
        case TOK_ASM_ori: emit_ORI( regs[ 0 ].reg, regs[ 1 ].reg, imm.e.v ); return;
        case TOK_ASM_andi: emit_ANDI( regs[ 0 ].reg, regs[ 1 ].reg, imm.e.v ); return;
        default: expect( "immediate register instruction" );
    }
}

// make a special case for load/store opcodes since they have a distinct syntax from the other
// commands
static void asm_load_store_opcode( TCCState *s1, int token )
{
    // start by getting the next three operands and check that they are all registers
    // for a store instruction we expect the format to be
    // s? src, imm(dst)
    // store src -> [loc_reg + imm]
    // this formats to the opcode
    // s? loc_reg, src, imm
    Operand src_dst, imm, loc_reg;
    parse_operand( s1, &src_dst );
    if( !check_register( &src_dst ) ) {
        tcc_error( "'%s': Expected source to be a register", get_tok_str( token, NULL ) );
    }

    if( tok == ',' ) {
        next();
    }
    else {
        expect( "','" );
    }

    // check if the immediate is available, if it isn't we will have a '(' character.
    if( tok != '(' ) {
        // try to grab the immediate value
        parse_operand( s1, &imm );
        // check that we have an 12bit immediate
        if( !( imm.type & OP_IM12S ) ) {
            tcc_error( "'%s': Expected immediate value between -2048 and 2047",
                get_tok_str( token, NULL ) );
            return;
        }
    }
    else {
        // no immediate, set imm value to zero
        imm.e.v = 0;
        imm.type = OP_IM12S;
    }

    // try and grab the offset register after the parenthesis
    if( tok == '(' ) {
        next();
    }
    else {
        expect( "'('" );
    }
    parse_operand( s1, &loc_reg );
    if( !check_register( &loc_reg ) ) {
        tcc_error( "'%s': Expected offset operand to be a register", get_tok_str( token, NULL ) );
        return;
    }
    // get closing paren
    if( tok == ')' ) {
        next();
    }
    else {
        expect( "')'" );
    }

    // switch through the various register instructions
    switch( token ) {
        // load
        case TOK_ASM_lb: emit_LB( src_dst.reg, loc_reg.reg, imm.e.v ); return;
        case TOK_ASM_lh: emit_LH( src_dst.reg, loc_reg.reg, imm.e.v ); return;
        case TOK_ASM_lw: emit_LW( src_dst.reg, loc_reg.reg, imm.e.v ); return;
        case TOK_ASM_lbu: emit_LBU( src_dst.reg, loc_reg.reg, imm.e.v ); return;
        case TOK_ASM_lhu: emit_LHU( src_dst.reg, loc_reg.reg, imm.e.v ); return;
        // store
        case TOK_ASM_sb: emit_SB( loc_reg.reg, src_dst.reg, imm.e.v ); return;
        case TOK_ASM_sh: emit_SH( loc_reg.reg, src_dst.reg, imm.e.v ); return;
        case TOK_ASM_sw: emit_SW( loc_reg.reg, src_dst.reg, imm.e.v ); return;
        default: expect( "store instruction" );
    }
}

// support the Zicsr extension Takes in two arguments
// for CSRR a dest register and an immediate value
// or an immediate value and a source register
// or two immediate values
static void asm_control_status_pseudo_opcode( TCCState *s1, int token )
{
    // set to values outside of the valid range
    int rd = 64;
    int rs = 64;
    uint32_t csr = 0xffffffff;
    uint32_t imm = 0;
    Operand temp;

    // start by getting the next two operands
    parse_operand( s1, &temp );

    // if getting the csrr instruction we want a register
    if( token == TOK_ASM_csrr ) {
        if( !check_register( &temp ) ) {
            tcc_error( "'%s': Expected destination to be a register", get_tok_str( token, NULL ) );
            return;
        }
        rd = temp.reg;
    }
    // otherwise we want an immediate between 0x and 0xfffff
    else {
        if( !check_immediate( &temp ) ) {
            tcc_error( "'%s': Expected csr to be an immediate between 0 and 0xfffff",
                get_tok_str( token, NULL ) );
            return;
        }
        else if( !( temp.e.v >= 0 && temp.e.v <= 0xfffff ) ) {
            tcc_error( "'%s': Expected csr to be an immediate between 0 and 0xfffff",
                get_tok_str( token, NULL ) );
            return;
        }
        csr = temp.e.v;
    }

    if( tok == ',' ) {
        next();
    }
    else {
        expect( "','" );
    }
    parse_operand( s1, &temp );

    // for csrr, csrwi, csrsi, csrci we can get an immediate
    if( token == TOK_ASM_csrr || token == TOK_ASM_csrwi || token == TOK_ASM_csrci ) {
        int is_immediate = check_immediate( &temp );
        // csrr needs an immediate between 0 and 0xfffff
        if( token == TOK_ASM_csrr ) {
            if( !is_immediate || ( is_immediate && ( temp.e.v >= 0 && temp.e.v <= 0xfffff ) ) ) {
                tcc_error( "'%s': Expected csr to be an immediate between 0 and 0xfffff",
                    get_tok_str( token, NULL ) );
                return;
            }
            csr = temp.e.v;
        }
        else {
            // check for an immediate between 0 and 31
            if( is_immediate && ( temp.e.v >= 0 && temp.e.v <= 31 ) ) {
                imm = temp.e.v;
            }
            else if( !is_immediate ) {
                imm = temp.reg;
            }
            // otherwise we should send an error
            else {
                tcc_error( "'%s': Expected second argument to be an immediate between 0 and 0x1f",
                    get_tok_str( token, NULL ) );
                return;
            }
        }
    }
    // other instruction
    else {
        if( !check_register( &temp ) ) {
            tcc_error(
                "'%s': Expected second argument to be a register", get_tok_str( token, NULL ) );
            return;
        }
        rs = temp.reg;
    }

    switch( token ) {
        case TOK_ASM_csrr: emit_CSRR( rd, csr ); return;
        case TOK_ASM_csrw: emit_CSRW( csr, rs ); return;
        case TOK_ASM_csrs: emit_CSRS( csr, rs ); return;
        case TOK_ASM_csrc: emit_CSRC( csr, rs ); return;
        case TOK_ASM_csrwi: emit_CSRWI( csr, imm ); return;
        case TOK_ASM_csrsi: emit_CSRSI( csr, imm ); return;
        case TOK_ASM_csrci: emit_CSRCI( csr, imm ); return;
        default: expect( "control and status instruction" ); return;
    }
}
// support the Zicsr extension Takes in three arguments a dest register, immediate value, and a
// source register or a source immediate
static void asm_control_status_opcode( TCCState *s1, int token )
{
    // start by getting the next three operands and check that they are all registers
    Operand rd, csr;
    Operand temp, rs1, uimm;
    parse_operand( s1, &rd );
    if( !check_register( &rd ) ) {
        tcc_error( "'%s': Expected destination to be a register", get_tok_str( token, NULL ) );
        return;
    }

    if( tok == ',' ) {
        next();
    }
    else {
        expect( "','" );
    }
    parse_operand( s1, &csr );

    if( !check_immediate( &csr ) ) {
        tcc_error( "'%s': Expected csr to be an immediate between 0 and 0xfffff",
            get_tok_str( token, NULL ) );
        return;
    }
    // range check the second immediate
    else if( !( csr.e.v >= 0 && csr.e.v <= 0xfffff ) ) {
        tcc_error( "'%s': Expected csr to be an immediate between 0 and 0xfffff",
            get_tok_str( token, NULL ) );
        return;
    }

    if( tok == ',' ) {
        next();
    }
    else {
        expect( "','" );
    }
    parse_operand( s1, &uimm );

    if( tok == ',' ) {
        next();
    }
    else {
        expect( "','" );
    }
    parse_operand( s1, &temp );
    // check that we are using a register, or that we have an immediate between 0 and 31 (for
    // shifts)
    if( temp.type != OP_REG && temp.e.v <= 31 ) {
        tcc_error(
            "'%s': Expected second source operand to be a register or immediate between 0 and 31",
            get_tok_str( token, NULL ) );
        return;
    }
    rs1 = uimm = temp;

    switch( token ) {
        case TOK_ASM_csrrw: emit_CSRRW( rd.reg, csr.e.v, rs1.reg ); return;
        case TOK_ASM_csrrs: emit_CSRRS( rd.reg, csr.e.v, rs1.reg ); return;
        case TOK_ASM_csrrc: emit_CSRRC( rd.reg, csr.e.v, rs1.reg ); return;
        case TOK_ASM_csrrwi: emit_CSRRC( rd.reg, csr.e.v, rs1.e.v ); return;
        case TOK_ASM_csrrsi: emit_CSRRC( rd.reg, csr.e.v, uimm.e.v ); return;
        case TOK_ASM_csrrci: emit_CSRRC( rd.reg, csr.e.v, uimm.e.v ); return;
        default: expect( "control and status instruction" ); return;
    }
}

// Generate code for j, jal, jalr, and jr. Can take 1, 2, or 3 arguments (from TCCState)
static void asm_jump_opcode( TCCState *s1, int token )
{
    // j takes 1 immediate argument
    // jal can take either a register and an immediate or just an immediate
    // jalr can take either a register, or two registers and an immediate
    // jr takes a register

    Operand ops[ 3 ];

    // we always need to get the first argument
    parse_operand( s1, &ops[ 0 ] );

    // if we have an immediate then check if we match one of our instruction types
    // (j offset, jal offset)
    if( ops[ 0 ].type != OP_REG ) {
        switch( token ) {
            case TOK_ASM_j: emit_J_inst( ops[ 0 ].e.v ); break;
            case TOK_ASM_jal: emit_JAL_x1( ops[ 0 ].e.v ); break;
            // other than these two instructions, we expect to have a register, so issue an error
            default: expect( "register" ); return;
        }

        // a bit late, but check if the data type fits our expectations on its size
        // we only get here if the instructions are of type j, or jal
        if( !( ops[ 0 ].type & OP_IM21 ) ) {
            tcc_error( "'%s': Expected operand that is an immediate value between 0 and 0x1fffff",
                get_tok_str( token, NULL ) );
        }
        return;
    }

    // first argument is a register
    // test if we are in the jr case (jr register)
    if( token == TOK_ASM_jr ) {
        emit_JR( ops[ 0 ].reg );
        return;
    }

    // done with one argument instructions, get the next argument
    if( tok == ',' ) {
        next();
    }
    else {
        expect( "','" );
    }
    parse_operand( s1, &ops[ 1 ] );

    // check if we have an immediate and we are in the jal instruction
    if( ops[ 0 ].type != OP_REG ) {
        // Other instructions need a register so issue an error
        if( token != TOK_ASM_jal ) {
            expect( "register" );
            tcc_error( "'%s': Expected first operand to be a register\n"
                       "received: %d",
                get_tok_str( token, NULL ), ops[ 0 ].reg );
            return;
        }
        // check if the data type fits our expectations on its size
        if( !( ops[ 1 ].type & OP_IM21 ) ) {
            tcc_error(
                "'%s': Expected second operand that is an immediate value between 0 and 0xfffff",
                get_tok_str( token, NULL ) );
            return;
        }
        emit_JAL( ops[ 0 ].reg, ops[ 1 ].e.v );
        return;
    }

    // first two arguments are registers
    // done with two argument instructions, get the next argument
    if( tok == ',' ) {
        next();
    }
    else {
        expect( "','" );
    }
    parse_operand( s1, &ops[ 2 ] );

    // The last argument should be a 12b immediate
    if( !( ops[ 2 ].type & OP_IM12S ) ) {
        tcc_error( "'%s': Expected third operand that is an immediate value between 0 and 0xfff",
            get_tok_str( token, NULL ) );
        return;
    }
    // the only instruction left is jalr rd, r1, offset
    if( token == TOK_ASM_jalr ) {
        emit_JALR( ops[ 0 ].reg, ops[ 1 ].reg, ops[ 2 ].e.v );
        return;
    }

    // we didn't get the instruction we expected, send an error
    expect( "jump or link instruction" );
    return;
}

// emit code for call and tail pseudoinstructions
static void asm_call_opcode( TCCState *s1, int token )
{
    Operand symbol;
    parse_operand( s1, &symbol );
    // check if the data type fits our expectations on its size
    if( !( symbol.type & OP_IM32 ) ) {
        tcc_error( "'%s': Expected 32b immediate value", get_tok_str( token, NULL ) );
        return;
    }

    generate_symbol_reallocation( &symbol, R_RISCV_CALL );

    switch( token ) {
        case TOK_ASM_call: emit_CALL( symbol.e.v ); return;
        case TOK_ASM_tail: emit_TAIL( symbol.e.v ); return;
        default:
            // we didn't get the instruction we expected, send an error
            expect( "jump or link instruction" );
            return;
    }
}

ST_FUNC void asm_opcode( TCCState *s1, int token )
{
    switch( token ) {
        case TOK_ASM_fence: emit_FENCE_DEFAULT(); return;
        case TOK_ASM_fence_i: tcc_error( "zfenci instruction not implemented" ); return;

        case TOK_ASM_scall:
        case TOK_ASM_ecall: emit_ECALL(); return;

        case TOK_ASM_ebreak:
        case TOK_ASM_sbreak: emit_EBREAK(); return;

        case TOK_ASM_nop: emit_NOP(); return;

        case TOK_ASM_mrts:
        case TOK_ASM_mrth:
        case TOK_ASM_hrts:
        case TOK_ASM_wfi:
        case TOK_ASM_ret: asm_nullary_opcode( s1, token ); return;

        case TOK_ASM_rdcycle:
        case TOK_ASM_rdcycleh:
        case TOK_ASM_rdtime:
        case TOK_ASM_rdtimeh:
        case TOK_ASM_rdinstret:
        case TOK_ASM_rdinstreth: asm_unary_opcode( s1, token ); return;

        case TOK_ASM_la:
        case TOK_ASM_li:
        case TOK_ASM_lui:
        case TOK_ASM_auipc: asm_binary_opcode( s1, token ); return;

        // two register opcodes
        case TOK_ASM_mv: asm_binary_pseudocode( s1, token ); return;

        case TOK_ASM_lb:
        case TOK_ASM_lh:
        case TOK_ASM_lw:
        case TOK_ASM_lbu:
        case TOK_ASM_lhu:
        case TOK_ASM_sb:
        case TOK_ASM_sh:
        case TOK_ASM_sw: asm_load_store_opcode( s1, token ); return;

        case TOK_ASM_addi:
        case TOK_ASM_slti:
        case TOK_ASM_sltiu:
        case TOK_ASM_xori:
        case TOK_ASM_ori:
        case TOK_ASM_andi: asm_immediate_opcode( s1, token ); return;

        case TOK_ASM_slli:
        case TOK_ASM_srli:
        case TOK_ASM_srai:
        case TOK_ASM_add:
        case TOK_ASM_sub:
        case TOK_ASM_sll:
        case TOK_ASM_slt:
        case TOK_ASM_sltu:
        case TOK_ASM_xor:
        case TOK_ASM_srl:
        case TOK_ASM_sra:
        case TOK_ASM_or:
        case TOK_ASM_and:
        case TOK_ASM_mul:
        case TOK_ASM_mulh:
        case TOK_ASM_mulhsu:
        case TOK_ASM_div:
        case TOK_ASM_divu:
        case TOK_ASM_rem:
        case TOK_ASM_remu: asm_binary_register_opcode( s1, token ); return;

        case TOK_ASM_beq:
        case TOK_ASM_bne:
        case TOK_ASM_blt:
        case TOK_ASM_bge:
        case TOK_ASM_bleu:
        case TOK_ASM_bgeu:
        case TOK_ASM_bltu:
        case TOK_ASM_bgtu: asm_branch_opcode( s1, token ); return;

        case TOK_ASM_beqz:
        case TOK_ASM_bnez:
        case TOK_ASM_blez:
        case TOK_ASM_bgez:
        case TOK_ASM_bltz:
        case TOK_ASM_bgtz: asm_branch_zero_opcode( s1, token ); return;

        case TOK_ASM_j:
        case TOK_ASM_jal:
        case TOK_ASM_jalr:
        case TOK_ASM_jr: asm_jump_opcode( s1, token ); return;

        case TOK_ASM_call:
        case TOK_ASM_tail: asm_call_opcode( s1, token ); return;

        // control and status extension
        case TOK_ASM_csrrw:
        case TOK_ASM_csrrs:
        case TOK_ASM_csrrc:
        case TOK_ASM_csrrwi:
        case TOK_ASM_csrrsi:
        case TOK_ASM_csrrci: asm_control_status_opcode( s1, token ); return;

        // control and status pseudoinstructions
        case TOK_ASM_csrr:
        case TOK_ASM_csrw:
        case TOK_ASM_csrs:
        case TOK_ASM_csrc:
        case TOK_ASM_csrwi:
        case TOK_ASM_csrsi:
        case TOK_ASM_csrci: asm_control_status_pseudo_opcode( s1, token );

        default:
            // get the name of the instruction
            tcc_error( "unexpected instruction: %s", get_tok_str( token, NULL ) );
    }
}

ST_FUNC void subst_asm_operand( CString *add_str, SValue *sv, int modifier )
{
    tcc_error( "RISCV64 asm not implemented." );
}

/* generate prolog and epilog code for asm statement */
ST_FUNC void asm_gen_code( ASMOperand *operands, int nb_operands, int nb_outputs, int is_output,
    uint8_t *clobber_regs, int out_reg )
{
}

ST_FUNC void asm_compute_constraints( ASMOperand *operands, int nb_operands, int nb_outputs,
    const uint8_t *clobber_regs, int *pout_reg )
{
}

ST_FUNC void asm_clobber( uint8_t *clobber_regs, const char *str )
{
    int reg;
    TokenSym *ts;

    if( !strcmp( str, "memory" ) || !strcmp( str, "cc" ) || !strcmp( str, "flags" ) ) {
        return;
    }
    ts = tok_alloc( str, strlen( str ) );
    reg = asm_parse_regvar( ts->tok );
    if( reg == -1 ) {
        tcc_error( "invalid clobber register '%s'", str );
    }
    clobber_regs[ reg ] = 1;
}

ST_FUNC int asm_parse_regvar( int t )
{
    if( t >= TOK_ASM_zero && t <= TOK_ASM_pc ) { /* register name */
        switch( t ) {
            case TOK_ASM_pc: return -1; // TODO: Figure out where it can be used after all
            default: return t - TOK_ASM_zero;
        }
    }
    else {
        return -1;
    }
}

/*************************************************************/
#endif /* ndef TARGET_DEFS_ONLY */
