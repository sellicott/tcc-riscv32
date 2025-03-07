int printf( const char *, ... );
char t[] = "012345678";

int main( void )
{
    char *data = t;
    unsigned long long r = 4;
    unsigned a = 5;
    unsigned long long b = 12;

    asm( "nop; nop; nop;" );
    unsigned long long c = 0;
    unsigned long long d = 1;
    unsigned long long e = 0;
    asm( "nop; nop; nop;" );


    *(unsigned *)( data + r ) += a - b;
    printf( "data = \"%s\"\n", data );

    // print starting values
    printf( "c = \"%llx\", d = \"%llx\", e = \"%llx\"\n", c, d, e );
    printf( "c = \"%llx\", ", c );
    printf( "d = \"%llx\", ", d );
    printf( "e = \"%llx\"\n", e );
    printf( "c = \"%llx\", d = \"%llx\", e = \"%llx\"\n\n", c, d, e );

    // try and overflow the lower part of a 32-bit variable
    // test carry
    asm( "nop; nop; nop;" );
    c = 0xffffffff;
    asm( "nop; nop; nop;" );
    e = c + d;
    printf( "c = \"%llx\", d = \"%llx\", e = \"%llx\"\n", c, d, e );
    printf( "c = \"%llx\", ", c );
    printf( "d = \"%llx\", ", d );
    printf( "e = \"%llx\"\n", e );
    printf( "c = \"%llx\", d = \"%llx\", e = \"%llx\"\n\n", c, d, e );

    // try and underflow the lower part of a 32-bit variable
    // test carry
    c = 0x100000000;
    e = c - d;
    printf( "c = \"%llx\", d = \"%llx\", e = \"%llx\"\n", c, d, e );
    printf( "c = \"%llx\", ", c );
    printf( "d = \"%llx\", ", d );
    printf( "e = \"%llx\"\n", e );
    printf( "c = \"%llx\", d = \"%llx\", e = \"%llx\"\n\n", c, d, e );

    return 0;
}
