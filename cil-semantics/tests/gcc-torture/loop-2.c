void exit(int status);
void abort(void);
int a[2];

void f (b)
{
  unsigned int i;
  for (i = 0; i < b; i++)
    a[i] = i - 2;
}

int main ()
{
  a[0] = a[1] = 0;
  f (2);
  if (a[0] != -2 || a[1] != -1)
    abort ();
  exit (0);
}
