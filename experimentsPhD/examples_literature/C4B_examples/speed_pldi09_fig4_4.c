#include "assert.h"

void peed_pldi09_fig4_4(int n, int m)
{
  int i=n;

  assert(0 < m);

  while (i > 0) {
    if (i < m)
      i=i-1;
    else
      i=i-m;
  }
}
