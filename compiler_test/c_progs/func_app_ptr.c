#include <stdio.h>

// Define a function
int add(int x, int y) {
    return x + y;
}

int sub(int x, int y) {
    return x - y;
}

int main() {
    int (*x)(int, int);
    x = add;
    int r = x(5,3);
    x = sub;
    r = x(5,3);
    return r;
}

