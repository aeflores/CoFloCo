#include "assert.h"


void start(int n, int m)
{
  int va=n;
  int vb=0;

/* assert(n > 0); */
  assert(m > 0);

  while (va > 0) {
    if (vb < m) { 
      vb=vb+1; 
      va=va-1;
    } else {
      vb=vb-1;
      vb=0;
    }
  }
}

