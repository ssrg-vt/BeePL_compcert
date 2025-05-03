#include <stdio.h>

// Define a function
int add(int x, int y) {
    return x + y;
}

int main() {
    int (*x)(int, int) = add;
    int r = x(3,4);
    return r;
}

