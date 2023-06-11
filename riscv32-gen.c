#ifdef TARGET_DEFS_ONLY

// Number of registers available to allocator:
#ifdef TCC_TARGET_RISCV32_ilp32
// TODO add temporary and saved registers here once I figure out how TCC works
#define NB_REGS 11 // a0-a7, sp (?), ra, sp
#else
#define NB_REGS 19 // a0-a7, fa0-fa7, xxx, ra, sp
#endif
#define NB_ASM_REGS 32
#define CONFIG_TCC_ASM

#define TREG_R( x ) ( x ) // x = 0..7
#define TREG_F( x ) ( x + 8 ) // x = 0..7

// Register classes sorted from more general to more precise:
#define RC_INT ( 1 << 0 )
#define RC_FLOAT ( 1 << 1 )
#define RC_R( x ) ( 1 << ( 2 + ( x ) ) ) // x = 0..7
#define RC_F( x ) ( 1 << ( 10 + ( x ) ) ) // x = 0..7

#define RC_IRET ( RC_R( 0 ) ) // int return register class
#define RC_IRE2 ( RC_R( 1 ) ) // int 2nd return register class
#define RC_FRET ( RC_F( 0 ) ) // float return register class

#define REG_IRET ( TREG_R( 0 ) ) // int return register number
#define REG_IRE2 ( TREG_R( 1 ) ) // int 2nd return register number
#define REG_FRET ( TREG_F( 0 ) ) // float return register number

#define PTR_SIZE 4

#define LDOUBLE_SIZE 16
#define LDOUBLE_ALIGN 16

#define MAX_ALIGN 16

#define CHAR_IS_UNSIGNED

#else
#define USING_GLOBALS
#include "riscv_utils.h"
#include "tcc.h"
#include <assert.h>

#ifdef TCC_RISCV_ilp32
ST_DATA const char *const target_machine_defs = "__riscv\0"
                                                "__riscv_xlen 32\0"
                                                "__riscv_div\0"
                                                "__riscv_mul\0"
                                                "__riscv_float_abi_soft\0";
#else
ST_DATA const char *const target_machine_defs = "__riscv\0"
                                                "__riscv_xlen 32\0"
                                                "__riscv_flen 32\0"
                                                "__riscv_div\0"
                                                "__riscv_mul\0"
                                                "__riscv_fdiv\0"
                                                "__riscv_fsqrt\0"
                                                "__riscv_float_abi_double\0";
#endif

#define XLEN 4

#define TREG_RA 17
#define TREG_SP 18

ST_DATA const int reg_classes[ NB_REGS ] = {
    // Integer Function Arguments
    RC_INT | RC_R( 0 ), RC_INT | RC_R( 1 ), RC_INT | RC_R( 2 ), RC_INT | RC_R( 3 ),
    RC_INT | RC_R( 4 ), RC_INT | RC_R( 5 ), RC_INT | RC_R( 6 ), RC_INT | RC_R( 7 ),
#ifndef TCC_TARGET_RISCV32_ilp32
    // Floating point function arguments
    RC_FLOAT | RC_F( 0 ), RC_FLOAT | RC_F( 1 ), RC_FLOAT | RC_F( 2 ), RC_FLOAT | RC_F( 3 ),
    RC_FLOAT | RC_F( 4 ), RC_FLOAT | RC_F( 5 ), RC_FLOAT | RC_F( 6 ), RC_FLOAT | RC_F( 7 ),
#endif
    0, 1 << TREG_RA, 1 << TREG_SP };

#if defined( CONFIG_TCC_BCHECK )
static addr_t func_bound_offset;
static unsigned long func_bound_ind;
ST_DATA int func_bound_add_epilog;
#endif

static int ireg( int r )
{
    if( r == TREG_RA )
        return 1; // ra
    if( r == TREG_SP )
        return 2; // sp
    assert( r >= 0 && r < 8 );
    return r + 10; // tccrX --> aX == x(10+X)
}

static int is_ireg( int r )
{
    return (unsigned)r < 8 || r == TREG_RA || r == TREG_SP;
}

static int freg( int r )
{
    assert( r >= 8 && r < 16 );
    return r - 8 + 10; // tccfX --> faX == f(10+X)
}

static int is_freg( int r )
{
#ifndef TCC_TARGET_RISCV32_ilp32
    return r >= 8 && r < 16;
#else
    // there are no floating point registers in rv32imc isa
    return 0;
#endif
}

// ---------------------- opcode helper functions ------------------------------------------------//

ST_FUNC void o( unsigned int opcode )
{
    int ind1 = ind + 4;
    if( nocode_wanted ) {
        return;
    }
    if( ind1 > cur_text_section->data_allocated ) {
        section_realloc( cur_text_section, ind1 );
    }
    write32le( cur_text_section->data + ind, opcode );
    ind = ind1;
}

static void EIu( uint32_t opcode, uint32_t func3, uint32_t rd, uint32_t rs1, uint32_t imm )
{
    o( opcode | ( func3 << 12 ) | ( rd << 7 ) | ( rs1 << 15 ) | ( imm << 20 ) );
}

static void ER(
    uint32_t opcode, uint32_t func3, uint32_t rd, uint32_t rs1, uint32_t rs2, uint32_t func7 )
{
    o( opcode | func3 << 12 | rd << 7 | rs1 << 15 | rs2 << 20 | func7 << 25 );
}

static void EI( uint32_t opcode, uint32_t func3, uint32_t rd, uint32_t rs1, uint32_t imm )
{
    assert( !( ( imm + ( 1 << 11 ) ) >> 12 ) );
    EIu( opcode, func3, rd, rs1, imm );
}

static void ES( uint32_t opcode, uint32_t func3, uint32_t rs1, uint32_t rs2, uint32_t imm )
{
    assert( !( ( imm + ( 1 << 11 ) ) >> 12 ) );
    o( opcode | ( func3 << 12 ) | ( ( imm & 0x1f ) << 7 ) | ( rs1 << 15 ) | ( rs2 << 20 ) |
        ( ( imm >> 5 ) << 25 ) );
}

static int load_symofs( int r, SValue *sv, int forstore )
{
    int doload = 0;
    int t0 = 5; // t0 = x5 = 5
    int rd; // return register
    int sv_constant = sv->c.i; // stack value constant
    int stack_value = sv->r & VT_VALMASK; // stack value

    rd = is_ireg( r ) ? ireg( r ) : t0; // default register is t0

    // check if we are dealing with a named symbol
    if( sv->r & VT_SYM ) {
        addr_t addend = 0; // offset value when generating a relocation entry
        int type;
        Sym label = { 0 };
        doload = 1;
        label.type.t = VT_VOID | VT_STATIC;

        assert( stack_value == VT_CONST );

        if( LARGE_IMM( sv_constant ) ) {
            tcc_error( "unimp: large addend for global address (0x%lx)", (long)sv_constant );
        }

        if( sv->sym->type.t & VT_STATIC ) { // XXX do this per linker relax
            addend = sv_constant;
            sv->c.i = 0;
            // offset is probably loaded already, we don't need to generate a load in this case 
            doload = 0; 
        }

        // generate a relocation entry with the generated offset
        greloca( cur_text_section, sv->sym, ind, R_RISCV_PCREL_HI20, addend );

        put_extern_sym( &label, cur_text_section, ind, 0 );
        // immediate value is 0 so that the linker can load values into it
        emit_AUIPC( rd, 0 ); 

        type = ( doload || !forstore ) ? R_RISCV_PCREL_LO12_I : R_RISCV_PCREL_LO12_S;
        greloca( cur_text_section, &label, ind, type, 0 );

        if( doload ) {
            emit_ADDI( rd, rd, 0 ); // lw RR, 0(RR)
        }
    }
    else if( stack_value == VT_LOCAL || stack_value == VT_LLOCAL ) {
        int s0;
        s0 = 8; // s0
        rd = s0;
        if( sv_constant != sv->c.i ) {
            tcc_error( "unimp: store(giant local off) (0x%lx)", (long)sv->c.i );
        }
        if( LARGE_IMM( sv_constant ) ) {
            sv->c.i = IMM_LOW( sv_constant );
            emit_LUI( rd, IMM_HIGH( sv_constant + 0x800 ) );
            emit_ADD( rd, rd, s0 );
        }
    }
    else {
        tcc_error( "uhh" );
    }
    return rd;
}

static void load_large_constant( int rr, int fc, uint32_t pi )
{
    if( fc < 0 )
        pi++;
    emit_LUI( rr, IMM_HIGH( pi ) );
    emit_ADDI( rr, rr, IMM_LOW( pi ) );
    emit_SLLI( rr, rr, 12 );
    emit_ADDI( rr, rr, IMM_LOW( fc ) );
    emit_SLLI( rr, rr, 12 );
    emit_ADDI( rr, rr, IMM_LOW( fc ) );
    emit_SLLI( rr, rr, 8 );
}

/*
 * Similar to load this takes a stack value (sv) and stores it into a register (r)
 * However, we know that the thing on the stack is an lvalue (it has a name) and therefore
 * in order to move it to a register we need to get the address of the named thing
 */
static void load_lvalue( int r, SValue *sv )
{
    // get the actual physical register we want to store stuff into
    int dest_reg = is_ireg( r ) ? ireg( r ) : freg( r ); // rr
    int lvar_offset = sv->c.i; // fc
    int stack_type = sv->type.t & VT_BTYPE; // bt
    int stack_reg = sv->r; // fr
    int masked_stack_reg = stack_reg & VT_VALMASK; // v
    int align, rs1;

    int size = type_size( &sv->type, &align );

    assert( !is_freg( r ) || stack_type == VT_FLOAT || stack_type == VT_DOUBLE );
    if( stack_type == VT_FUNC ) { /* XXX should be done in generic code */
        size = PTR_SIZE;
    }

    if( is_float( sv->type.t ) ) {
        tcc_internal_error( "floating point not implemented" );
    }

    if( masked_stack_reg == VT_LOCAL || ( stack_reg & VT_SYM ) ) {
        rs1 = load_symofs( r, sv, 0 );
        lvar_offset = sv->c.i;
    }
    // case where our lvalue location is stored in a register
    else if( masked_stack_reg < VT_CONST ) {
        rs1 = ireg( masked_stack_reg );
        lvar_offset = 0; // XXX store ofs in LVAL(reg)
    }
    else if( masked_stack_reg == VT_LLOCAL ) {
        rs1 = load_symofs( r, sv, 0 );
        lvar_offset = sv->c.i;
        emit_LW( dest_reg, rs1, lvar_offset );
        rs1 = dest_reg;
        lvar_offset = 0;
    }
    else if( masked_stack_reg == VT_CONST ) {
        int64_t si = sv->c.i;
        si >>= 32;
        if( si != 0 ) {
            load_large_constant( dest_reg, lvar_offset, si );
            lvar_offset &= 0xff;
        }
        else {
            emit_LUI( dest_reg, IMM_HIGH( lvar_offset ) );
            lvar_offset = IMM_LOW( lvar_offset );
        }
        rs1 = dest_reg;
    }
    else {
        tcc_error( "unimp: load(non-local lval)" );
    }
    // TODO handle floating pont, 64-bit values, and 128-bit values
    switch( size ) {
        case 1: emit_LB( dest_reg, rs1, lvar_offset ); break;
        case 2: emit_LH( dest_reg, rs1, lvar_offset ); break;
        case 4: emit_LW( dest_reg, rs1, lvar_offset ); break;
        default: tcc_error( "unexpected load size: %d", size );
    }
}

/*
 * load a stack value into a register meaning we need to put the thing stored in sv into r
 * r is the register we want to load stuff into, and sv is the tcc stack value
 *
 * this function also handles generating comparison and branch instructions
 * we need to check what the type of stack value we have is since we might need to do drastically
 * different things depending on whether sv is an lvalue (i.e. a pointer to the thing we want)
 */
ST_FUNC void load( int r, SValue *sv )
{
    int dest_reg = is_ireg( r ) ? ireg( r ) : freg( r );
    int lvar_offset = sv->c.i; // fc
    int stack_type = sv->type.t & VT_BTYPE; // bt
    int stack_reg = sv->r; // fr
    int masked_stack_reg = stack_reg & VT_VALMASK; // v

    // loading to an lvalue i.e. pointer into register
    if( stack_reg & VT_LVAL ) {
        load_lvalue( r, sv );
    }
    else if( masked_stack_reg == VT_CONST ) {
        int rs1 = 0, zext = 0;
        int do32bit = 32;

        // only handle integer types
        if( is_float( sv->type.t ) ) {
            tcc_error( "unimp: load(float)" );
        }

        assert( !is_float( sv->type.t ) && is_ireg( r ) );
        // We need to add Svalue.sym to the constant
        if( stack_reg & VT_SYM ) {
            rs1 = load_symofs( r, sv, 0 );
            lvar_offset = sv->c.i;
            do32bit = 0;
        }

        // load large constant
        if( lvar_offset != sv->c.i ) {
            int64_t si = sv->c.i;
            si >>= 32;
            if( si != 0 ) {
                load_large_constant( dest_reg, lvar_offset, si );
                lvar_offset &= 0xff;
                rs1 = dest_reg;
                do32bit = 0;
            }
            else if( stack_type == VT_LLONG ) {
                /* A 32bit unsigned constant for a 64bit type.
                   lui always sign extends, so we need to do an explicit zext.*/
                zext = 1;
            }
        }

        if( LARGE_IMM( lvar_offset ) ) {
            rs1 = dest_reg;
            // add 0x800 so when the lower (sign extended) bits get added, they don't ruin things
            emit_LUI( dest_reg, IMM_HIGH( lvar_offset + 0x800 )  );
        }
        if( lvar_offset || ( dest_reg != rs1 ) || do32bit || ( stack_reg & VT_SYM ) ) {
            // EI(0x13 | do32bit, 0, rd, rs1, lvar_offset << 20 >> 20); // addi[w] R, x0|R,
            // lvar_offset
            emit_ADDI( dest_reg, rs1, IMM_LOW( lvar_offset ) );
        }
        if( zext ) {
            emit_SLLI( dest_reg, dest_reg, 31 );
            emit_SRLI( dest_reg, dest_reg, 31 );
            tcc_internal_error( "I think this code is broken" );
        }
    }
    else if( masked_stack_reg == VT_LOCAL ) {
        int br = load_symofs( r, sv, 0 );
        assert( is_ireg( r ) );
        lvar_offset = sv->c.i;
        emit_ADDI( dest_reg, br, lvar_offset );
    }
    else if( masked_stack_reg < VT_CONST ) { /* reg-reg */
        // assert(!lvar_offset); XXX support offseted regs
        if( is_freg( r ) && is_freg( masked_stack_reg ) ) {
            ER( 0x53, 0, dest_reg, freg( masked_stack_reg ), freg( masked_stack_reg ),
                stack_type == VT_DOUBLE ? 0x11 : 0x10 ); // fsgnj.[sd] Rd, V, V == fmv.[sd] Rd, V
            tcc_internal_error( "things be happening" );
        }
        else if( is_ireg( r ) && is_ireg( masked_stack_reg ) ) {
            emit_ADDI( dest_reg, ireg( masked_stack_reg ), 0 );
        }
        else {
            tcc_error( "Floating point not implemented in riscv32" );
        }
    }
    // Value is stored in the CPU flag from a comparison operation. Put it in a safe place.
    else if( masked_stack_reg == VT_CMP ) {
        int op = vtop->cmp_op;
        int a = vtop->cmp_r & 0xff;
        int b = ( vtop->cmp_r >> 8 ) & 0xff;
        int inv = 0;
        // TODO cleanup this code so that it uses more of the pseudo operation
        switch( op ) {
            case TOK_ULT:
            case TOK_UGE:
            case TOK_ULE:
            case TOK_UGT:
            case TOK_LT:
            case TOK_GE:
            case TOK_LE:
            case TOK_GT:
                if( op & 1 ) { // remove [U]GE,GT
                    inv = 1;
                    op--;
                }
                if( ( op & 7 ) == 6 ) { // [U]LE
                    int t = a;
                    a = b;
                    b = t;
                    inv ^= 1;
                }
                //ER( 0x33, ( op > TOK_UGT ) ? 2 : 3, dest_reg, a, b, 0 ); // slt[u] d, a, b
                if( op > TOK_UGT ) {
                    emit_SLT( dest_reg, a, b );
                }
                else {
                    emit_SLTU( dest_reg, a, b );
                }
                if( inv ) {
                    emit_XORI( dest_reg, dest_reg, 1 );
                } // xori d, d, 1
                break;
            case TOK_NE:
            case TOK_EQ:
                // we only need to subtract if the comparison isn't already against zero
                // we check if the comparison is against zero by checking if the two source registers
                // are different from the destination
                if( dest_reg != a || b ) {
                    emit_SUB( dest_reg, a, b ); // sub d, a, b
                }
                if( op == TOK_NE ) {
                    emit_SNEZ( dest_reg, dest_reg ); // sltu d, x0, d == snez d,d
                }
                else {
                    emit_SEQZ( dest_reg, dest_reg ); // sltiu d, d, 1 == seqz d,d
                }
                break;
        }
    }
    else if( ( masked_stack_reg & ~1 ) == VT_JMP ) {
        int t = masked_stack_reg & 1;
        assert( is_ireg( r ) );
        emit_ADDI( dest_reg, 0, t ); // addi Rd, x0, t
        gjmp_addr( ind + 8 );
        gsym( lvar_offset );
        emit_ADDI( dest_reg, 0, t ^ 1 ); // addi Rd, x0, !t
    }
    else {
        tcc_error( "unimp: load(non-const)" );
    }
}

/*
 * Store: push a value from a register (r) onto the top of the stack
 * The top of the stack should be an lvalue (a pointer to somewhere in memory)
 */
ST_FUNC void store( int r, SValue *sv )
{
    int stack_reg = sv->r;
    int stack_reg_type = stack_reg & VT_VALMASK;
    int stack_type = sv->type.t & VT_BTYPE;

    int src_reg = is_ireg( r ) ? ireg( r ) : freg( r );
    int loc_reg = 8; // s0
    int offset = sv->c.i;

    // Get the size and alignment of the stack value we are writing to
    int align;
    int size = type_size( &sv->type, &align );

    // Make sure we can perform the operation (if floating point)
    assert( !is_float( stack_type ) || is_freg( r ) || stack_type == VT_LDOUBLE );

    /* long doubles are in two integer registers, but the load/store
       primitives only deal with one, so do as if it's one reg.  */
    if( stack_type == VT_LDOUBLE ) {
        size = align = 8;
    }
    if( stack_type == VT_STRUCT ) {
        tcc_error( "unimp: store(struct)" );
    }
    if( size > 8 ) {
        tcc_error( "unimp: large sized store" );
    }

    // Load the correct address into the loc_reg register
    assert( stack_reg & VT_LVAL );
    if( stack_reg_type == VT_LOCAL || ( stack_reg & VT_SYM ) ) {
        loc_reg = load_symofs( -1, sv, 1 );
        offset = sv->c.i;
    }
    else if( stack_reg_type < VT_CONST ) {
        loc_reg = ireg( stack_reg_type );
        offset = 0; // XXX support offsets regs
    }
    else if( stack_reg_type == VT_CONST ) {
        uint64_t offset_hi = ( sv->c.i >> 32 );
        if( offset_hi != 0 ) {
            load_large_constant( loc_reg, offset, offset_hi );
            offset &= 0xff;
        }
        else {
            //lui RR, upper(fc)
            emit_LUI( loc_reg, IMM_HIGH( offset ) );
            offset = IMM_LOW( offset );
        }
    }
    else {
        tcc_error( "implement me: %s(!local)", __FUNCTION__ );
    }

    if( is_freg( r ) ) {
        tcc_error( "unip: floating point" );
    }

    // load the value from the source register into the location pointed to by
    // loc_reg
    // TODO: store floating point, 64-bit, and 128-bit values
    switch( size ) {
        case 1: emit_SB( loc_reg, src_reg, offset ); break;
        case 2: emit_SH( loc_reg, src_reg, offset ); break;
        case 4: emit_SW( loc_reg, src_reg, offset ); break;
        default: tcc_error( "unexpected store size: %d", size );
    }
}

static void gcall_or_jmp( int docall )
{
    int tr = docall ? 1 : 5; // ra or t0
    if( ( vtop->r & ( VT_VALMASK | VT_LVAL ) ) == VT_CONST &&
        ( ( vtop->r & VT_SYM ) && vtop->c.i == (int)vtop->c.i ) ) {
        /* constant symbolic case -> simple relocation */
        greloca( cur_text_section, vtop->sym, ind, R_RISCV_CALL_PLT, (int)vtop->c.i );
        // auipc TR, 0 %call(func)
        // jalr  TR, r(TR)
        emit_AUIPC( tr, 0 );
        emit_JALR( tr, tr, 0 );
    }
    else if( vtop->r < VT_CONST ) {
        int r = ireg( vtop->r );
        emit_JALR( tr, r, 0 );
    }
    else {
        int r = TREG_RA;
        load( r, vtop );
        r = ireg( r );
        emit_JALR( tr, r, 0 );
    }
}

#if defined( CONFIG_TCC_BCHECK )

static void gen_bounds_call( int v )
{
    Sym *sym = external_helper_sym( v );

    greloca( cur_text_section, sym, ind, R_RISCV_CALL_PLT, 0 );
    o( 0x17 | ( 1 << 7 ) ); // auipc TR, 0 %call(func)
    EI( 0x67, 0, 1, 1, 0 ); // jalr  TR, r(TR)
}

static void gen_bounds_prolog( void )
{
    tcc_error( "no bounds checking" );
    /* leave some room for bound checking code */
    func_bound_offset = lbounds_section->data_offset;
    func_bound_ind = ind;
    func_bound_add_epilog = 0;
    o( 0x00000013 ); /* ld a0,#lbound section pointer */
    o( 0x00000013 );
    o( 0x00000013 ); /* nop -> call __bound_local_new */
    o( 0x00000013 );
}

static void gen_bounds_epilog( void )
{
    addr_t saved_ind;
    addr_t *bounds_ptr;
    Sym *sym_data;
    Sym label = { 0 };
    int offset_modified = func_bound_offset != lbounds_section->data_offset;

    tcc_error( "no bounds checking" );

    if( !offset_modified && !func_bound_add_epilog )
        return;

    /* add end of table info */
    bounds_ptr = section_ptr_add( lbounds_section, sizeof( addr_t ) );
    *bounds_ptr = 0;

    sym_data = get_sym_ref(
        &char_pointer_type, lbounds_section, func_bound_offset, lbounds_section->data_offset );

    label.type.t = VT_VOID | VT_STATIC;
    /* generate bound local allocation */
    if( offset_modified ) {
        saved_ind = ind;
        ind = func_bound_ind;
        put_extern_sym( &label, cur_text_section, ind, 0 );
        greloca( cur_text_section, sym_data, ind, R_RISCV_PCREL_HI20, 0 );
        o( 0x17 | ( 10 << 7 ) ); // auipc a0, 0 %pcrel_hi(sym)+addend
        greloca( cur_text_section, &label, ind, R_RISCV_PCREL_LO12_I, 0 );
        EI( 0x03, 2, 10, 10, 0 ); // lw a0, 0(a0)
        gen_bounds_call( TOK___bound_local_new );
        ind = saved_ind;
        label.c = 0; /* force new local ELF symbol */
    }

    /* generate bound check local freeing */
    o( 0xe02a1101 ); /* addi sp,sp,-32  sd   a0,0(sp)   */
    o( 0xa82ae42e ); /* sd   a1,8(sp)   fsd  fa0,16(sp) */
    put_extern_sym( &label, cur_text_section, ind, 0 );
    greloca( cur_text_section, sym_data, ind, R_RISCV_PCREL_HI20, 0 );
    o( 0x17 | ( 10 << 7 ) ); // auipc a0, 0 %pcrel_hi(sym)+addend
    greloca( cur_text_section, &label, ind, R_RISCV_PCREL_LO12_I, 0 );
    EI( 0x03, 2, 10, 10, 0 ); // lw a0, 0(a0)
    gen_bounds_call( TOK___bound_local_delete );
    o( 0x65a26502 ); /* ld   a0,0(sp)   ld   a1,8(sp)   */
    o( 0x61052542 ); /* fld  fa0,16(sp) addi sp,sp,32   */
}
#endif

static void reg_pass_rec( CType *type, int *rc, int *fieldofs, int ofs )
{
    if( ( type->t & VT_BTYPE ) == VT_STRUCT ) {
        Sym *f;
        if( type->ref->type.t == VT_UNION )
            rc[ 0 ] = -1;
        else
            for( f = type->ref->next; f; f = f->next )
                reg_pass_rec( &f->type, rc, fieldofs, ofs + f->c );
    }
    else if( type->t & VT_ARRAY ) {
        if( type->ref->c < 0 || type->ref->c > 2 )
            rc[ 0 ] = -1;
        else {
            int a, sz = type_size( &type->ref->type, &a );
            reg_pass_rec( &type->ref->type, rc, fieldofs, ofs );
            if( rc[ 0 ] > 2 || ( rc[ 0 ] == 2 && type->ref->c > 1 ) )
                rc[ 0 ] = -1;
            else if( type->ref->c == 2 && rc[ 0 ] && rc[ 1 ] == RC_FLOAT ) {
                rc[ ++rc[ 0 ] ] = RC_FLOAT;
                fieldofs[ rc[ 0 ] ] = ( ( ofs + sz ) << 4 ) | ( type->ref->type.t & VT_BTYPE );
            }
            else if( type->ref->c == 2 )
                rc[ 0 ] = -1;
        }
    }
    else if( rc[ 0 ] == 2 || rc[ 0 ] < 0 || ( type->t & VT_BTYPE ) == VT_LDOUBLE )
        rc[ 0 ] = -1;
    else if( !rc[ 0 ] || rc[ 1 ] == RC_FLOAT || is_float( type->t ) ) {
        rc[ ++rc[ 0 ] ] = is_float( type->t ) ? RC_FLOAT : RC_INT;
        fieldofs[ rc[ 0 ] ] =
            ( ofs << 4 ) | ( ( type->t & VT_BTYPE ) == VT_PTR ? VT_LLONG : type->t & VT_BTYPE );
    }
    else
        rc[ 0 ] = -1;
}

static void reg_pass( CType *type, int *prc, int *fieldofs, int named )
{
    prc[ 0 ] = 0;
    reg_pass_rec( type, prc, fieldofs, 0 );
    if( prc[ 0 ] <= 0 || !named ) {
        int align, size = type_size( type, &align );
        prc[ 0 ] = ( size + 7 ) >> 3;
        prc[ 1 ] = prc[ 2 ] = RC_INT;
        fieldofs[ 1 ] = ( 0 << 4 ) | ( size <= 1     ? VT_BYTE
                                         : size <= 2 ? VT_SHORT
                                         : size <= 4 ? VT_INT
                                                     : VT_LLONG );
        fieldofs[ 2 ] = ( 8 << 4 ) | ( size <= 9      ? VT_BYTE
                                         : size <= 10 ? VT_SHORT
                                         : size <= 12 ? VT_INT
                                                      : VT_LLONG );
    }
}

ST_FUNC void gfunc_call( int nb_args )
{
    int i, align, size, areg[ 2 ];
    int *info = tcc_malloc( ( nb_args + 1 ) * sizeof( int ) );
    int stack_adj = 0, tempspace = 0, stack_add, ofs, splitofs = 0;
    SValue *sv;
    Sym *sa;
    const uint32_t t0 = 5;
    const uint32_t sp = 2;

#ifdef CONFIG_TCC_BCHECK
    int bc_save = tcc_state->do_bounds_check;
    if( tcc_state->do_bounds_check )
        gbound_args( nb_args );
#endif

    areg[ 0 ] = 0; /* int arg regs */
    areg[ 1 ] = 8; /* float arg regs */
    sa = vtop[ -nb_args ].type.ref->next;
    for( i = 0; i < nb_args; i++ ) {
        int nregs, byref = 0, tempofs;
        int prc[ 3 ], fieldofs[ 3 ];
        sv = &vtop[ 1 + i - nb_args ];
        sv->type.t &= ~VT_ARRAY; // XXX this should be done in tccgen.c
        size = type_size( &sv->type, &align );
        if( size > 16 ) {
            align = ( align < XLEN ) ? align : XLEN;
            tempspace = ( tempspace + align - 1 ) & -align;
            tempofs = tempspace;
            tempspace += size;
            size = align = 8;
            byref = 64 | ( tempofs << 7 );
        }
        reg_pass( &sv->type, prc, fieldofs, sa != 0 );
        if( !sa && align == 2 * XLEN && size <= 2 * XLEN ) {
            areg[ 0 ] = ( areg[ 0 ] + 1 ) & ~1;
        }
        nregs = prc[ 0 ];
        if( size == 0 ) {
            info[ i ] = 0;
        }
        else if( ( prc[ 1 ] == RC_INT && areg[ 0 ] >= 8 ) ||
                 ( prc[ 1 ] == RC_FLOAT && areg[ 1 ] >= 16 ) ||
                 ( nregs == 2 && prc[ 1 ] == RC_FLOAT && prc[ 2 ] == RC_FLOAT &&
                     areg[ 1 ] >= 15 ) ||
                 ( nregs == 2 && prc[ 1 ] != prc[ 2 ] && ( areg[ 1 ] >= 16 || areg[ 0 ] >= 8 ) ) ) {
            info[ i ] = 32;
            if( align < XLEN )
                align = XLEN;
            stack_adj += ( size + align - 1 ) & -align;
            if( !sa ) /* one vararg on stack forces the rest on stack */
                areg[ 0 ] = 8, areg[ 1 ] = 16;
        }
        else {
            info[ i ] = areg[ prc[ 1 ] - 1 ]++;
            if( !byref )
                info[ i ] |= ( fieldofs[ 1 ] & VT_BTYPE ) << 12;
            assert( !( fieldofs[ 1 ] >> 4 ) );
            if( nregs == 2 ) {
                if( prc[ 2 ] == RC_FLOAT || areg[ 0 ] < 8 )
                    info[ i ] |= ( 1 + areg[ prc[ 2 ] - 1 ]++ ) << 7;
                else {
                    info[ i ] |= 16;
                    stack_adj += 8;
                }
                if( !byref ) {
                    assert( ( fieldofs[ 2 ] >> 4 ) < 2048 );
                    info[ i ] |= fieldofs[ 2 ] << ( 12 + 4 ); // includes offset
                }
            }
        }
        info[ i ] |= byref;
        if( sa )
            sa = sa->next;
    }
    stack_adj = ( stack_adj + 15 ) & -16;
    tempspace = ( tempspace + 15 ) & -16;
    stack_add = stack_adj + tempspace;

    /* fetch cpu flag before generating any code */
    if( ( vtop->r & VT_VALMASK ) == VT_CMP )
        gv( RC_INT );

    if( stack_add ) {
        if( stack_add >= 0x1000 ) {
            emit_LUI( t0, IMM_HIGH( -stack_add ) );
            emit_ADDI( t0, t0, IMM_LOW( -stack_add ) );
            emit_ADD( sp, sp, t0 );
        }
        else {
            emit_ADDI( sp, sp, IMM_LOW( -stack_add ) );
        }
        for( i = ofs = 0; i < nb_args; i++ ) {
            if( info[ i ] & ( 64 | 32 ) ) {
                vrotb( nb_args - i );
                size = type_size( &vtop->type, &align );
                if( info[ i ] & 64 ) {
                    vset( &char_pointer_type, TREG_SP, 0 );
                    vpushi( stack_adj + ( info[ i ] >> 7 ) );
                    gen_op( '+' );
                    vpushv( vtop ); // this replaces the old argument
                    vrott( 3 );
                    indir();
                    vtop->type = vtop[ -1 ].type;
                    vswap();
                    vstore();
                    vpop();
                    size = align = 8;
                }
                if( info[ i ] & 32 ) {
                    if( align < XLEN )
                        align = XLEN;
                    /* Once we support offseted regs we can do this:
                       vset(&vtop->type, TREG_SP | VT_LVAL, ofs);
                       to construct the lvalue for the outgoing stack slot,
                       until then we have to jump through hoops.  */
                    vset( &char_pointer_type, TREG_SP, 0 );
                    ofs = ( ofs + align - 1 ) & -align;
                    vpushi( ofs );
                    gen_op( '+' );
                    indir();
                    vtop->type = vtop[ -1 ].type;
                    vswap();
                    vstore();
                    vtop->r = vtop->r2 = VT_CONST; // this arg is done
                    ofs += size;
                }
                vrott( nb_args - i );
            }
            else if( info[ i ] & 16 ) {
                assert( !splitofs );
                splitofs = ofs;
                ofs += 4;
            }
        }
    }
    for( i = 0; i < nb_args; i++ ) {
        int ii = info[ nb_args - 1 - i ], r = ii, r2 = r;
        if( !( r & 32 ) ) {
            CType origtype;
            int loadt;
            r &= 15;
            r2 = r2 & 64 ? 0 : ( r2 >> 7 ) & 31;
            assert( r2 <= 16 );
            vrotb( i + 1 );
            origtype = vtop->type;
            size = type_size( &vtop->type, &align );
            if( size == 0 )
                goto done;
            loadt = vtop->type.t & VT_BTYPE;
            if( loadt == VT_STRUCT ) {
                loadt = ( ii >> 12 ) & VT_BTYPE;
            }
            if( info[ nb_args - 1 - i ] & 16 ) {
                assert( !r2 );
                r2 = 1 + TREG_RA;
            }
            if( loadt == VT_LDOUBLE ) {
                assert( r2 );
                r2--;
            }
            else if( r2 ) {
                test_lvalue();
                vpushv( vtop );
            }
            vtop->type.t = loadt | ( vtop->type.t & VT_UNSIGNED );
            gv( r < 8 ? RC_R( r ) : RC_F( r - 8 ) );
            vtop->type = origtype;

            if( r2 && loadt != VT_LDOUBLE ) {
                r2--;
                assert( r2 < 16 || r2 == TREG_RA );
                vswap();
                gaddrof();
                vtop->type = char_pointer_type;
                vpushi( ii >> 20 );
#ifdef CONFIG_TCC_BCHECK
                if( ( origtype.t & VT_BTYPE ) == VT_STRUCT ) {
                    tcc_state->do_bounds_check = 0;
                }
#endif
                gen_op( '+' );
#ifdef CONFIG_TCC_BCHECK
                tcc_state->do_bounds_check = bc_save;
#endif
                indir();
                vtop->type = origtype;
                loadt = vtop->type.t & VT_BTYPE;
                if( loadt == VT_STRUCT ) {
                    loadt = ( ii >> 16 ) & VT_BTYPE;
                }
                save_reg_upstack( r2, 1 );
                vtop->type.t = loadt | ( vtop->type.t & VT_UNSIGNED );
                load( r2, vtop );
                assert( r2 < VT_CONST );
                vtop--;
                vtop->r2 = r2;
            }
            if( info[ nb_args - 1 - i ] & 16 ) {
                // ES(0x23, 3, 2, ireg(vtop->r2), splitofs); // sd t0, ofs(sp)
                emit_SW( ireg( vtop->r2 ), 5, splitofs );
                vtop->r2 = VT_CONST;
            }
            else if( loadt == VT_LDOUBLE && vtop->r2 != r2 ) {
                assert( vtop->r2 <= 7 && r2 <= 7 );
                /* XXX we'd like to have 'gv' move directly into
                   the right class instead of us fixing it up.  */
                // mv Ra+1, RR2
                emit_MV( ireg( r2 ), ireg( vtop->r2 ) );
                vtop->r2 = r2;
            }
        done:
            vrott( i + 1 );
        }
    }
    vrotb( nb_args + 1 );
    save_regs( nb_args + 1 );
    gcall_or_jmp( 1 );
    vtop -= nb_args + 1;
    if( stack_add ) {
        const uint32_t t0 = 5;
        const uint32_t sp = 2;
        if( stack_add >= 0x1000 ) {
            emit_LUI( t0, IMM_HIGH( stack_add ) );
            emit_ADDI( t0, t0, IMM_LOW( stack_add ) );
            emit_ADD( sp, sp, t0 );
        }
        else {
            emit_ADDI( sp, sp, stack_add );
        }
    }
    tcc_free( info );
}

static int func_sub_sp_offset, num_va_regs, func_va_list_ofs;

ST_FUNC void gfunc_prolog( Sym *func_sym )
{
    CType *func_type = &func_sym->type;
    int i, addr, align, size;
    int param_addr = 0;
    int areg[ 2 ];
    Sym *sym;
    CType *type;

    sym = func_type->ref;
    loc = -16; // for ra and s0
    func_sub_sp_offset = ind;
    ind += 5 * 4;

    areg[ 0 ] = 0; 
    areg[ 1 ] = 0;
    addr = 0;
    /* if the function returns by reference, then add an
       implicit pointer parameter */
    size = type_size( &func_vt, &align );
    if( size > 2 * XLEN ) {
        int s0 = 8;
        int loc_reg = s0; // s0
        int src_reg = ireg( areg[ 0 ]++ );

        loc -= 8;
        func_vc = loc;

        emit_SW( loc_reg, src_reg, loc );
        tcc_internal_error( "I don't think we are handling this case correctly" );
    }
    /* define parameters */
    while( ( sym = sym->next ) != NULL ) {
        int byref = 0;
        int regcount;
        int prc[ 3 ], fieldofs[ 3 ];
        type = &sym->type;
        size = type_size( type, &align );
        if( size > 2 * XLEN ) {
            type = &char_pointer_type;
            size = align = byref = 8;
        }
        reg_pass( type, prc, fieldofs, 1 );
        regcount = prc[ 0 ];
        if( areg[ prc[ 1 ] - 1 ] >= 8 ||
            ( regcount == 2 &&
                ( ( prc[ 1 ] == RC_FLOAT && prc[ 2 ] == RC_FLOAT && areg[ 1 ] >= 7 ) ||
                    ( prc[ 1 ] != prc[ 2 ] && ( areg[ 1 ] >= 8 || areg[ 0 ] >= 8 ) ) ) ) ) {
            if( align < XLEN )
                align = XLEN;
            addr = ( addr + align - 1 ) & -align;
            param_addr = addr;
            addr += size;
        }
        else {
            loc -= regcount * 8; // XXX could reserve only 'size' bytes
            // loc -= regcount * PTR_SIZE; // XXX could reserve only 'size' bytes
            param_addr = loc;
            for( i = 0; i < regcount; i++ ) {
                const uint32_t t0 = 5;
                const uint32_t s0 = 8;
                if( areg[ prc[ 1 + i ] - 1 ] >= 8 ) {
                    assert( i == 1 && regcount == 2 && !( addr & 7 ) );
                    emit_LW( t0, s0, addr );
                    addr += XLEN;
                    emit_SW( s0, t0, loc + i * 4 );
                }
                else if( prc[ 1 + i ] == RC_FLOAT ) {
                    // emit_S(0x22, (size / regcount) == 4 ? 2 : 3, 8, 10 + areg[1]++, loc +
                    // (fieldofs[i+1] >> 4)); // fs[wd] FAi, loc(s0)
                    tcc_error( "unimp: floating point support" );
                }
                else {
                    // sw aX, loc(s0) // XXX
                    emit_SW( s0, ireg( areg[ 0 ]++ ), loc + i * XLEN );
                }
            }
        }
        sym_push( sym->v & ~SYM_FIELD, &sym->type, ( byref ? VT_LLOCAL : VT_LOCAL ) | VT_LVAL,
            param_addr );
    }
    func_va_list_ofs = addr;
    num_va_regs = 0;
    if( func_var ) {
        const uint32_t s0 = 8;
        for( ; areg[ 0 ] < 8; areg[ 0 ]++ ) {
            num_va_regs++;
            // ES(0x23, 2, 8, 10 + areg[0], -8 + num_va_regs * 8); // sw aX, loc(s0)
            emit_SW( s0, ireg( areg[ 0 ] ), -8 + num_va_regs * 8 );
        }
    }
#ifdef CONFIG_TCC_BCHECK
    if( tcc_state->do_bounds_check )
        gen_bounds_prolog();
#endif
}

ST_FUNC int gfunc_sret( CType *vt, int variadic, CType *ret, int *ret_align, int *regsize )
{
    int align, size = type_size( vt, &align ), nregs;
    int prc[ 3 ], fieldofs[ 3 ];
    *ret_align = 1;
    *regsize = 8;
    if( size > 16 )
        return 0;
    reg_pass( vt, prc, fieldofs, 1 );
    nregs = prc[ 0 ];
    if( nregs == 2 && prc[ 1 ] != prc[ 2 ] )
        return -1; /* generic code can't deal with this case */
    if( prc[ 1 ] == RC_FLOAT ) {
        *regsize = size / nregs;
    }
    ret->t = fieldofs[ 1 ] & VT_BTYPE;
    ret->ref = NULL;
    return nregs;
}

ST_FUNC void arch_transfer_ret_regs( int aftercall )
{
    int prc[ 3 ], fieldofs[ 3 ];
    reg_pass( &vtop->type, prc, fieldofs, 1 );
    assert( prc[ 0 ] == 2 && prc[ 1 ] != prc[ 2 ] && !( fieldofs[ 1 ] >> 4 ) );
    assert( vtop->r == ( VT_LOCAL | VT_LVAL ) );
    vpushv( vtop );
    vtop->type.t = fieldofs[ 1 ] & VT_BTYPE;
    ( aftercall ? store : load )( prc[ 1 ] == RC_INT ? REG_IRET : REG_FRET, vtop );
    vtop->c.i += fieldofs[ 2 ] >> 4;
    vtop->type.t = fieldofs[ 2 ] & VT_BTYPE;
    ( aftercall ? store : load )( prc[ 2 ] == RC_INT ? REG_IRET : REG_FRET, vtop );
    vtop--;
}

ST_FUNC void gfunc_epilog( void )
{
    int v, saved_ind, d, large_ofs_ind;
    const uint32_t ra = 1;
    const uint32_t sp = 2;
    const uint32_t t0 = 5;
    const uint32_t s0 = 8;

#ifdef CONFIG_TCC_BCHECK
    if( tcc_state->do_bounds_check )
        gen_bounds_epilog();
#endif

    loc = ( loc - num_va_regs * PTR_SIZE );
    d = v = ( -loc + 15 ) & -16;


    if( v >= ( 1 << 11 ) ) {
        d = 16;
        emit_LI(t0, v)
        emit_ADD( sp, sp, t0 );
    }

    emit_LW( ra, sp, d - PTR_SIZE - ( num_va_regs * PTR_SIZE ) );
    emit_LW( s0, sp, d - 2 * PTR_SIZE - ( num_va_regs * PTR_SIZE ) );
    emit_ADDI( sp, sp, d );
    emit_RET();
    large_ofs_ind = ind;
    if( v >= ( 1 << 11 ) ) {
        emit_ADDI( s0, sp, d - num_va_regs * PTR_SIZE );
        emit_LI( t0, v );
        emit_SUB( sp, sp, t0 );
        gjmp_addr( func_sub_sp_offset + 5 * 4 );
    }
    saved_ind = ind;

    ind = func_sub_sp_offset;
    emit_ADDI(sp, sp, -d);
    emit_SW(sp, ra, d - PTR_SIZE - num_va_regs * PTR_SIZE);
    emit_SW(sp, s0, d - 2*PTR_SIZE - num_va_regs * PTR_SIZE);

    if( v < ( 1 << 11 ) )
        emit_ADDI( s0, sp, d - num_va_regs * PTR_SIZE );
    else
        gjmp_addr( large_ofs_ind );
    if( ( ind - func_sub_sp_offset ) != 5 * 4 )
        emit_NOP();
    ind = saved_ind;
}

ST_FUNC void gen_va_start( void )
{
    vtop--;
    vset( &char_pointer_type, VT_LOCAL, func_va_list_ofs );
}

ST_FUNC void gen_fill_nops( int bytes )
{
    if( ( bytes & 3 ) )
        tcc_error( "alignment of code section not multiple of 4" );
    while( bytes > 0 ) {
        emit_NOP();
        bytes -= 4;
    }
}

// Patch all branches in list "pointed to" by branch_list_offset to branch to target_offset:
ST_FUNC void gsym_addr( int branch_list_offset, int target_offset )
{
    uint32_t next_branch_offset = branch_list_offset;
    uint32_t target_offset_uint = target_offset;

    // hack so that we can use emmit_<opcode> macros to generate code
    // turn on code generation, but save the state so we can turn it off again if necessary
    int nocode_wanted_old = nocode_wanted; // save the old no code state
    int original_ind = ind;                // save the current pointer location
    nocode_wanted &= ~0x20000000;          // copy code from the NO_CODE macro (move to tcc.h?)

    while( next_branch_offset ) {
        int32_t rel_jmp;
        // set the current branch offset (the offset from the data section to write to).
        // Note that the ind variable is a global variable used to set the write location in the 
        // generation code it is the offset from cur_text_section->data
        ind = next_branch_offset; 
        // rel_jmp can have up to a +-1MiB range (20bits 0 to 0x1fffff)
        rel_jmp = target_offset_uint - ind;
        // get the location that we need to write our next value to.
        next_branch_offset = read32le(cur_text_section->data + ind);
        if( ( rel_jmp + ( 1 << 21 ) ) & ~( ( 1U << 22 ) - 2 ) ) {
            tcc_error("out-of-range branch chain (> +-1MiB): %#03x", rel_jmp);
        }
        // generate the jmp table
        if( rel_jmp == 4 ) {
            // we just need a nop as PC will increment by 4 for us (this will need to be updated
            // once compressed instructions are added)
            emit_NOP();
        }
        else {
            emit_J_inst( rel_jmp );
        }
    }

    // reset globals back to their original state
    nocode_wanted = nocode_wanted_old;
    ind = original_ind;
}

// Generate forward branch to label:
ST_FUNC int gjmp( int t )
{
    if( nocode_wanted )
        return t;
    // write zeros to the location to fill in later
    o( t );
    return ind - 4;
}

// Generate branch to known address:
ST_FUNC void gjmp_addr( int a )
{
    uint32_t rel_jmp = a - ind;
    // do we have a near jump or a far jump
    if( ( rel_jmp + ( 1 << 21 ) ) & ~( ( 1U << 22 ) - 2 ) ) {
        // far jump
        uint32_t t0 = 5;
        emit_LUI( t0, IMM_HIGH( rel_jmp + 0x800 ) );
        emit_JALR( 0, t0, IMM_LOW( rel_jmp ) << 20 >> 20); // sign extend masked value
    }
    else {
        // near jump
        emit_J_inst( rel_jmp );
    }
}

ST_FUNC int gjmp_cond( int op, int t )
{
    int tmp;
    int a = vtop->cmp_r & 0xff;
    int b = ( vtop->cmp_r >> 8 ) & 0xff;
    switch( op ) {
        case TOK_ULT: op = 6; break;
        case TOK_UGE: op = 7; break;
        case TOK_ULE:
            op = 7;
            tmp = a;
            a = b;
            b = tmp;
            break;
        case TOK_UGT:
            op = 6;
            tmp = a;
            a = b;
            b = tmp;
            break;
        case TOK_LT: op = 4; break;
        case TOK_GE: op = 5; break;
        case TOK_LE:
            op = 5;
            tmp = a;
            a = b;
            b = tmp;
            break;
        case TOK_GT:
            op = 4;
            tmp = a;
            a = b;
            b = tmp;
            break;
        case TOK_NE: op = 1; break;
        case TOK_EQ: op = 0; break;
    }
    o( 0x63 | ( op ^ 1 ) << 12 | a << 15 | b << 20 | 8 << 7 ); // bOP a,b,+4
    return gjmp( t );
}

ST_FUNC int gjmp_append( int n, int t )
{
    void *p;
    /* insert jump list n into t */
    if( n ) {
        uint32_t n1 = n, n2;
        while( ( n2 = read32le( p = cur_text_section->data + n1 ) ) ) n1 = n2;
        write32le( p, t );
        t = n;
    }
    return t;
}

static int gen_opi_immediate( int op, int fc, int ll );

// ll is set to 1 when generating 'long' code (64-bit stuff)
static void gen_opil( int op, int ll )
{
    int a, b, d;

    // handle the case where one of the values is a constant, use an immediate value if we can
    if( ( vtop->r & ( VT_VALMASK | VT_LVAL | VT_SYM ) ) == VT_CONST ) {
        int fc = vtop->c.i;
        if( fc == vtop->c.i && !( ( (unsigned)fc + ( 1 << 11 ) ) >> 12 ) ) {
            int use_register = gen_opi_immediate( op, fc, ll );

            // check if we were able to finish everything, or if more work is required
            if( !use_register ) {
                return;
            }
        }
    }
    gv2( RC_INT, RC_INT );
    a = ireg( vtop[ -1 ].r );
    b = ireg( vtop[ 0 ].r );
    vtop -= 2;
    d = get_reg( RC_INT );
    vtop++;
    vtop[ 0 ].r = d;
    d = ireg( d );
    switch( op ) {
        default:
            if( op >= TOK_ULT && op <= TOK_GT ) {
                vset_VT_CMP( op );
                vtop->cmp_r = a | b << 8;
                break;
            }
            tcc_error( "implement me: %s(%s)", __FUNCTION__, get_tok_str( op, NULL ) );
            break;

        case '+': emit_ADD( d, a, b ); break;
        case '-': emit_SUB( d, a, b ); break;
        case TOK_SAR: emit_SRA( d, a, b ); break;
        case TOK_SHR: emit_SRL( d, a, b ); break;
        case TOK_SHL: emit_SLL( d, a, b ); break;
        case '*': emit_MUL( d, a, b ); break;
        case '/': emit_DIV( d, a, b ); break;
        case '&': emit_AND( d, a, b ); break;
        case '^': emit_XOR( d, a, b ); break;
        case '|': emit_OR( d, a, b ); break;
        case '%': emit_REM( d, a, b ); break;
        case TOK_UMOD: emit_REMU( d, a, b ); break;
        case TOK_PDIV:
        case TOK_UDIV: emit_DIVU( d, a, b ); break;
    }
}

// generate instructions for binary operations where one of the values is a constant
// fc is the immediate constant
// returns 1 if we need to "fall through" and use the register generating code instead
// otherwise returns 0
static int gen_opi_immediate( int op, int fc, int ll )
{
    // get values from the main stack
    int a, d, rd;
    int m = 31;

    if( ll ) {
        tcc_error( "trying to emit 64bit instruction, gonna have a bad time" );
    }

    vswap();
    gv( RC_INT );
    a = ireg( vtop[ 0 ].r );
    --vtop;
    // d is tcc style register
    d = get_reg( RC_INT );
    // convert to riscv register
    rd = ireg( d );
    ++vtop;
    vswap();

    // TODO switch between 64bit and 32bit operations
    switch( op ) {
        case '-':
            // check if the immediate value is too big and use the registers instead
            if( fc <= -( 1 << 11 ) ) {
                return 1;
            }
            fc = -fc;
        case '+': emit_ADDI( rd, a, fc ); break;
        case TOK_LE:
            if( fc >= ( 1 << 11 ) - 1 ) {
                return 1;
            }
            ++fc;
        case TOK_LT: emit_SLTI( rd, a, fc ); break;
        case TOK_ULE:
            if( fc >= ( 1 << 11 ) - 1 || fc == -1 ) {
                return 1;
            }
            ++fc;
        case TOK_ULT: emit_SLTIU( rd, a, fc ); break;
        case '^': emit_XORI( rd, a, fc ); break;
        case '|': emit_ORI( rd, a, fc ); break;
        case '&': emit_ANDI( rd, a, fc ); break;
        case TOK_SHL:
            fc &= m;
            emit_SLLI( rd, a, fc );
            break;
        case TOK_SHR:
            fc &= m;
            emit_SRLI( rd, a, fc );
            break;
        case TOK_SAR:
            fc = 1024 | ( fc & m );
            emit_SRA( rd, a, fc );
            break;


        case TOK_UGE: /* -> TOK_ULT */
        case TOK_UGT: /* -> TOK_ULE */
        case TOK_GE: /* -> TOK_LT */
        case TOK_GT: /* -> TOK_LE */
            gen_opil( op - 1, 0 );
            vtop->cmp_op ^= 1;
            return 0;

        case TOK_NE:
        case TOK_EQ:
            if( fc ) {
                gen_opil( '-', 0 );
                a = ireg( vtop++->r );
            }
            --vtop;
            vset_VT_CMP( op );
            vtop->cmp_r = a | 0 << 8;
            return 0;
        default:
            /*
              default case means we have to bail, since otherwise we're pretending we handled it properly
              as an example, '*' will hit this if RHS is an immediate since RV32M doesn't have MULI,
              so we used to just... not actually compile a multiplication instruction in at all
            */
            return 1;
    }

    // push the value to the stack (general case)
    --vtop;
    if( op >= TOK_ULT && op <= TOK_GT ) {
        vset_VT_CMP( TOK_NE );
        vtop->cmp_r = ireg( d ) | 0 << 8;
    }
    else {
        vtop[ 0 ].r = d;
    }
    return 0;
}

ST_FUNC void gen_opi( int op )
{
    gen_opil( op, 0 );
}

#if PTR_SIZE == 8
ST_FUNC void gen_opl( int op )
{
    gen_opil( op, 1 );
}
#endif
ST_FUNC void gen_opf( int op )
{
    tcc_error( "Floating point not supported on riscv32" );
}

ST_FUNC void gen_cvt_sxtw( void )
{
    /* XXX on risc-v the registers are usually sign-extended already.
       Let's try to not do anything here.  */
}

#if defined( TCC_TARGET_RISCV32 )
// stubs for riscv32
ST_FUNC void gen_cvt_itof( int t )
{
    tcc_error( "No floating point support for riscv32" );
}

ST_FUNC void gen_cvt_ftoi( int t )
{
    tcc_error( "No floating point support for riscv32" );
}

ST_FUNC void gen_cvt_ftof( int dt )
{
    tcc_error( "No floating point support for riscv32" );
}

// riscv64
#else
ST_FUNC void gen_cvt_itof( int t )
{
    int rr = ireg( gv( RC_INT ) ), dr;
    int u = vtop->type.t & VT_UNSIGNED;
    int l = ( vtop->type.t & VT_BTYPE ) == VT_LLONG;
    if( t == VT_LDOUBLE ) {
        int func = l ? ( u ? TOK___floatunditf : TOK___floatditf )
                     : ( u ? TOK___floatunsitf : TOK___floatsitf );
        vpush_helper_func( func );
        vrott( 2 );
        gfunc_call( 1 );
        vpushi( 0 );
        vtop->type.t = t;
        vtop->r = REG_IRET;
        vtop->r2 = TREG_R( 1 );
    }
    else {
        vtop--;
        dr = get_reg( RC_FLOAT );
        vtop++;
        vtop->r = dr;
        dr = freg( dr );
        EI( 0x53, 7, dr, rr,
            ( ( 0x68 | ( t == VT_DOUBLE ? 1 : 0 ) ) << 5 ) | ( u ? 1 : 0 ) |
                ( l ? 2 : 0 ) ); // fcvt.[sd].[wl][u]
    }
}

ST_FUNC void gen_cvt_ftoi( int t )
{
    int ft = vtop->type.t & VT_BTYPE;
    int l = ( t & VT_BTYPE ) == VT_LLONG;
    int u = t & VT_UNSIGNED;
    if( ft == VT_LDOUBLE ) {
        int func =
            l ? ( u ? TOK___fixunstfdi : TOK___fixtfdi ) : ( u ? TOK___fixunstfsi : TOK___fixtfsi );
        vpush_helper_func( func );
        vrott( 2 );
        gfunc_call( 1 );
        vpushi( 0 );
        vtop->type.t = t;
        vtop->r = REG_IRET;
    }
    else {
        int rr = freg( gv( RC_FLOAT ) ), dr;
        vtop--;
        dr = get_reg( RC_INT );
        vtop++;
        vtop->r = dr;
        dr = ireg( dr );
        EI( 0x53, 1, dr, rr,
            ( ( 0x60 | ( ft == VT_DOUBLE ? 1 : 0 ) ) << 5 ) | ( u ? 1 : 0 ) |
                ( l ? 2 : 0 ) ); // fcvt.[wl][u].[sd] rtz
    }
}

#endif // TCC_TARGET_RISCV32

/* increment tcov counter */
ST_FUNC void gen_increment_tcov( SValue *sv )
{
    int r1, r2;
    Sym label = { 0 };
    label.type.t = VT_VOID | VT_STATIC;

    vpushv( sv );
    vtop->r = r1 = get_reg( RC_INT );
    r2 = get_reg( RC_INT );
    r1 = ireg( r1 );
    r2 = ireg( r2 );

    // this is a load global pseudo instruction
    greloca( cur_text_section, sv->sym, ind, R_RISCV_PCREL_HI20, 0 );
    put_extern_sym( &label, cur_text_section, ind, 0 );
    emit_AUIPC( r1, 0 );

    greloca( cur_text_section, &label, ind, R_RISCV_PCREL_LO12_I, 0 );
    emit_LW( r2, r1, 0 );

    emit_ADDI( r2, r2, 1 );

    // this is a store global pseudo instruction
    greloca( cur_text_section, sv->sym, ind, R_RISCV_PCREL_HI20, 0 );
    label.c = 0; /* force new local ELF symbol */
    put_extern_sym( &label, cur_text_section, ind, 0 );
    emit_AUIPC( r1, 0 );

    greloca( cur_text_section, &label, ind, R_RISCV_PCREL_LO12_S, 0 );
    emit_SW( r2, r1, 0 );
    vpop();
}

ST_FUNC void ggoto( void )
{
    gcall_or_jmp( 0 );
    vtop--;
}

ST_FUNC void gen_vla_sp_save( int addr )
{
    // ES(0x23, 3, 8, 2, addr); // sd sp, fc(s0)
    emit_SW( 8, 2, addr );
}

ST_FUNC void gen_vla_sp_restore( int addr )
{
    // EI(0x03, 3, 2, 8, addr); // ld sp, fc(s0)
    emit_LW( 2, 8, addr );
}

ST_FUNC void gen_vla_alloc( CType *type, int align )
{
    int rr;
#if defined( CONFIG_TCC_BCHECK )
    if( tcc_state->do_bounds_check )
        vpushv( vtop );
#endif
    rr = ireg( gv( RC_INT ) );
#if defined( CONFIG_TCC_BCHECK )
    if( tcc_state->do_bounds_check )
        EI( 0x13, 0, rr, rr, 15 + 1 ); // addi RR, RR, 15+1
    else
#endif
        EI( 0x13, 0, rr, rr, 15 ); // addi RR, RR, 15
    EI( 0x13, 7, rr, rr, -16 ); // andi, RR, RR, -16
    ER( 0x33, 0, 2, 2, rr, 0x20 ); // sub sp, sp, rr
    vpop();
#if defined( CONFIG_TCC_BCHECK )
    if( tcc_state->do_bounds_check ) {
        const uint32_t a0 = 10;
        const uint32_t sp = 2;

        vpushi( 0 );
        vtop->r = TREG_R( 0 );
        // o(0x00010513); /* mv a0,sp */
        emit_MV( a0, sp );
        vswap();
        vpush_helper_func( TOK___bound_new_region );
        vrott( 3 );
        gfunc_call( 2 );
        func_bound_add_epilog = 1;
    }
#endif
}
#endif
