#include <stdio.h>
#include <limits.h>

signed int id_si(signed int x) { return x; }
unsigned int id_ui(unsigned int x) { return x; }

signed char id_sc(signed char x) { return x; }
unsigned char id_uc(unsigned char x) { return x; }

signed short id_ss(signed short x) { return x; }
unsigned short id_us(unsigned short x) { return x; }

signed long long id_sll(signed long long x) { return x; }
unsigned long long id_ull(unsigned long long x) { return x; }

int main() {
    int res;

    // --- signed ---
    res = (id_si(5) == id_si(5));
    if (res) { printf("1 %d\n", res); }
    res = (id_si(5) == id_si(6));
    if (!res) { printf("2 %d\n", res); }

    res = (id_si(-5) != id_si(5));
    if (res) { printf("3 %d\n", res); }
    res = (id_si(-5) != id_si(-5));
    if (!res) { printf("4 %d\n", res); }

    res = (id_si(10) > id_si(5));
    if (res) { printf("5 %d\n", res); }
    res = (id_si(5) > id_si(10));
    if (!res) { printf("6 %d\n", res); }
    res = (id_si(-5) > id_si(-10));
    if (res) { printf("7 %d\n", res); }

    res = (id_si(5) < id_si(10));
    if (res) { printf("8 %d\n", res); }
    res = (id_si(10) < id_si(5));
    if (!res) { printf("9 %d\n", res); }
    res = (id_si(INT_MIN) < id_si(0));
    if (res) { printf("10 %d\n", res); }

    res = (id_si(6) >= id_si(5));
    if (res) { printf("11 %d\n", res); }
    res = (id_si(5) >= id_si(5));
    if (res) { printf("12 %d\n", res); }
    res = (id_si(4) >= id_si(5));
    if (!res) { printf("13 %d\n", res); }

    res = (id_si(4) <= id_si(5));
    if (res) { printf("14 %d\n", res); }
    res = (id_si(5) <= id_si(5));
    if (res) { printf("15 %d\n", res); }
    res = (id_si(6) <= id_si(5));
    if (!res) { printf("16 %d\n", res); }

    // --- unsigned ---
    res = (id_ui(5) < id_ui(10));
    if (res) { printf("17 %d\n", res); }
    res = (id_ui(UINT_MAX) > id_ui(10));
    if (res) { printf("18 %d\n", res); }
    res = (id_ui(10) < id_ui(5));
    if (!res) { printf("19 %d\n", res); }

    // --- different width ---
    res = (id_si(-1) < id_ui(1));
    if (!res) { printf("20 %d\n", res); }

    res = (id_si(-1) > id_ui(1));
    if (res) { printf("21 %d\n", res); }

    res = (id_si(0) == id_ui(0));
    if (res) { printf("22 %d\n", res); }

    res = (id_si(-10) > id_ui(5));
    if (res) { printf("23 %d\n", res); }

    // --- different signess ---
    res = (id_sc(-1) < id_uc(255));
    if (res) { printf("24 %d\n", res); }

    res = (id_ss(-1) > id_ui(1));
    if (res) { printf("25 %d\n", res); }

    res = (id_sll(-1LL) > id_ull(1ULL));
    if (res) { printf("26 %d\n", res); }
    res = (id_sll(-1LL) < id_ull(1ULL));
    if (!res) { printf("27 %d\n", res); }

    res = (id_si(100) == id_ui(100));
    if (res) { printf("28 %d\n", res); }

    // --- < <= and > >= ---

    // > >= signed
    res = (id_si(77) > id_si(77));
    if (!res) { printf("29 %d\n", res); }
    res = (id_si(77) >= id_si(77));
    if (res) { printf("30 %d\n", res); }

    // < <= signed
    res = (id_si(-22) < id_si(-22));
    if (!res) { printf("31 %d\n", res); }
    res = (id_si(-22) <= id_si(-22));
    if (res) { printf("32 %d\n", res); }

    // > >= unsigned
    res = (id_ui(99) > id_ui(99));
    if (!res) { printf("33 %d\n", res); }
    res = (id_ui(99) >= id_ui(99));
    if (res) { printf("34 %d\n", res); }

    // < <= unsigned
    res = (id_ui(0) < id_ui(0));
    if (!res) { printf("35 %d\n", res); }
    res = (id_ui(0) <= id_ui(0));
    if (res) { printf("36 %d\n", res); }

    return 0;
}