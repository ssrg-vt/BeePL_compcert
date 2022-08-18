/* Old-style, K&R function definitions */

#include <stdio.h>
#include <stdint.h>

void f(a, b, c)
     int c, a;
     char * b;
{
  printf("f(%d, \"%s\", %d)\n", a, b, c);
}

void g(a, b, c, d, e, x)
     const unsigned char a;
     char b[64];
     int c;
     uint64_t d;
     // volatile
     int e;
     long long x;
{
  printf("g(%li, \"%s\", %a, %a, %li, %lld)\n", a, b, c, d, e, x);
}

void h(a, b, c)
     char * b;
{
  printf("h(%d, \"%s\", %d)\n", a, b, c);
}


int main()
{
  f(1, "Hello", 2);
  g(257, "World", 3141592654, 3141592654, -34, 12345678901234567LL);
  h(6, "warning!", 7);
  return 0;
}

