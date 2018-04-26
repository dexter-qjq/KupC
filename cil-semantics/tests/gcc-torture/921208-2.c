void exit(int status);
void abort(void);
#define STACK_REQUIREMENT (100000 * 4 + 1024)
#if defined (STACK_SIZE) && STACK_SIZE < STACK_REQUIREMENT
int main () { exit (0); }
#else

void g(double a, double b){}

void f()
{
  int i;
  float a[100000];

  for (i = 0; i < 1; i++)
    {
      g(1.0, 1.0 + i / 2.0 * 3.0);
      g(2.0, 1.0 + i / 2.0 * 3.0);
    }
}

int main ()
{
  f();
  exit(0);
}

#endif
