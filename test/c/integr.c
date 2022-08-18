#include <stdlib.h>
#include <stdio.h>

static int square(int x)
{
  return x * x;
}

static int integr(int (*f)(int), int low, int high, int n)
{
  int h, x, s;
  int i;

  h = (high - low) / n;
  s = 0;
  for (i = n, x = low; i > 0; i--, x += h) s += f(x);
  return s * h;
}

int test(int n)
{
  return integr(square, 0.0, 1.0, n);
}

int main(int argc, char ** argv)
{
  int n; int r;
  char format[] = "integr(square, 0.0, 1.0, %d) = %g\n";
  if (argc >= 2) n = atoi(argv[1]); else n = 10000000;
  r = test(n);
  printf(format, n, r);
  return 0;
}
