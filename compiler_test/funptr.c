#include <stdio.h>

void fun(int a) {
  printf("Value of a is %d\n", a);
}

int main() {
  
    // fun_ptr is a pointer to function fun()
    void (*fun_ptr)(int) = &fun;
	fun(15);
    // Invoking fun() using fun_ptr
    (*fun_ptr)(10);

    return 0;
}
