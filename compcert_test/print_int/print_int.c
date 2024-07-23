#include <stdio.h>

/* 
void main() {
    int x = 5;
    printf("The integer value is %d", x);
}
*/

int main() {
    int x = 5;
    printf("The integer value is %d", x);
    return 0;
}

// compcert_test/print_int/print_int.c:3: warning: return type of 'main' should be 'int' [-Wmain-return-type]
// Because in CompCert, type can be int, long or float??

//./ccomp -D __bpf_helper_as_extern__ -S -o compcert_test/print_int/print_int.s compcert_test/print_int/print_int.c

// ./ccomp -D __bpf_helper_as_extern__ -interp compcert_test/print_int/print_int.c