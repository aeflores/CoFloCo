#include "assert.h"

void start(int n, int m, int dir)
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
