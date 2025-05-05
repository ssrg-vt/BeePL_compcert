unsigned int add(unsigned int x, unsigned int y)
{
  return x + y;
}

// Declare and initialize the function pointer statically
unsigned int (*fp)(unsigned int, unsigned int) = add;

unsigned int main(void)
{
  unsigned int a = 1U;
  unsigned int r = fp(a, a);
  return r;
}

