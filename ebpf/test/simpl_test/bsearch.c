#include <stdio.h>
#include <stdint.h>    

int bsearch(int tbl[100], int v) {
int l = 0, u = 99;
__builtin_annot("loop max 7");
while (l <= u) {
    int m = (l + u) / 2;
    __builtin_annot("entered with %1 = (0,99)", m);
    if (tbl[m] < v) l = m + 1;
    else if (tbl[m] > v) u = m - 1;
    else return m;
   }
return -1;
}

int main() {
    int tbl[100] = { 0 };
	bsearch(tbl, 2);
    return 0.0;
}

// ./ccomp -D __bpf_helper_as_extern__ -S -o ebpf/test/simpl_test/bsearch.s ebpf/test/simpl_test/bsearch.c

/* ./ccomp -D __bpf_helper_as_extern__ -interp ebpf/test/simpl_test/bsearch.c
Time 924: observable event: annotation "loop max 7" 
Time 951: observable event: annotation "entered with %1 = (0,99)" 49
Time 997: observable event: annotation "entered with %1 = (0,99)" 74
Time 1043: observable event: annotation "entered with %1 = (0,99)" 87
Time 1089: observable event: annotation "entered with %1 = (0,99)" 93
Time 1135: observable event: annotation "entered with %1 = (0,99)" 96
Time 1181: observable event: annotation "entered with %1 = (0,99)" 98
Time 1227: observable event: annotation "entered with %1 = (0,99)" 99
Time 1266: program terminated (exit code = 0)
*/
