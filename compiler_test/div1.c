#include <stdio.h>

short div(short x, short y) {
        return  x / y;
}

int main() {
        short r = div(8, 2);
        printf("%d", r); 
        return 0;
}
