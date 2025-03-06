int printf( const char *, ... );
char t[] = "012345678";

int main( void )
{
    char *data = t;
    unsigned long long r = 4;
    unsigned a = 5;
    unsigned long long b = 12;
    unsigned long long c = 0;
    unsigned long long d = 1;

    *(unsigned *)( data + r ) += a - b;
    printf( "data = \"%s\"\n", data );

    // try and overflow the lower part of a 32-bit variable
    // test carry
    c = 0xffffffff;
    c += d;
    printf( "c = \"%lld\"\n", c );

    // try and underflow the lower part of a 32-bit variable
    // test carry
    c = 0x100000000;
    c -= d;
    printf( "c = \"%lld\"\n", c );

    return 0;
}
