#include "stdio.h"
#define assert(x) if((x)){printf("good\n");}else{printf("bad\n");}
#define assertno(x) if((x)){printf("bad\n");}else{printf("good\n");}
int main(){
        float a = 0.1;
        assert(a > 0)
        assert(a < 1)
        assert(a >= 0.1)
        assert(a <= 1)
        assert(a <= 0.1f)
        assert(a == 0.1f)
        assert(a != 0.2f)
        printf("\n");
        assertno(a <= 0)
        assertno(a >= 1)
        assertno(a < 0.1)
        assertno(a > 1)
        assertno(a > 0.1f)
        assertno(a != 0.1f)
        assertno(a == 0.2f)
        printf("\n");
        double b = 0.1;
        assert(b > 0)
        assert(b < 1)
        assert(b >= 0.1)
        assert(b <= 1)
        assert(b <= 0.1)
        assert(b == 0.1)
        assert(b != 0.2)
        printf("\n");
        assertno(b <= 0)
        assertno(b >= 1)
        assertno(b < 0.1)
        assertno(b > 1)
        assertno(b > 0.1)
        assertno(b != 0.1)
        assertno(b == 0.2)
        printf("\ndone\n");
        return 0;
}
