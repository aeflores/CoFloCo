#include "assert.h"

void start(int x, int y)
{
  int z;

  assert(y >= 0);

  while (x > y) {
    x -= y+1;
    z = 100 + 2*y;
    while (z > 0)
      z--;
  }
}

