#include <stdio.h>
#include <stdlib.h>

int add(int x, int y) {
        return  x + y;
}

int main(int argc, char* argv[]) {

	int x, y;
	if (argc < 3) {
		printf("input two numbers\n");
		return -1;
	}

	x = atoi(argv[1]);
	y = atoi(argv[2]);
        int r = add(add(x,y), 5);
        return r;
}
