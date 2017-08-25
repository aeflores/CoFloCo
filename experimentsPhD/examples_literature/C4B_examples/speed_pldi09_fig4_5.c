#include "assert.h"

void peed_pldi09_fig4_5(int n, int m, int dir)
{
  int i;

  assert(0 < m);
  assert(m < n);

  i = m;

  while (0 < i && i < n) {
    if (dir == 1)
      i++;
    else
      i--;
  }
}
