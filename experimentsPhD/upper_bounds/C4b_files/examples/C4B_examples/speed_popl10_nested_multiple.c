int nondet();

void start(int x, int n, int y, int m)
{
  while (x<n) {
    while (y<m) {
      if (nondet()>0)
        break;
      y=y+1;
    }
    x=x+1;
  }
}
