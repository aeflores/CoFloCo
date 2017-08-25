int nondet();

void start(int n)
{
  while (n>0) {
    n=n-1;
    while (n>0) {
      if (nondet()>0) break;
      n=n-1;
    }
  }
}

