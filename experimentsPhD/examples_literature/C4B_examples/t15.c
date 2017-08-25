#include "assert.h"

void t15(int x, int y)
{
  int z;

  assert(y >= 0);

  while (x>y) {
    x-=y+1;
    for (z=y; z>0; z--)
      /* nothing */;
  }
}

