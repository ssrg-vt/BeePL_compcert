#include <stdio.h>

int add(int x, int y) {
	return	x + y;
}

int main() {
	add(add(1,2), 5);
	return 0;
}
