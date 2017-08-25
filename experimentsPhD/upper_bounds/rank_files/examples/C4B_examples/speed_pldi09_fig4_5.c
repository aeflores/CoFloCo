#include "assert.h"

void speed_pldi09_fig4_5(int n, int m, int dir)
{
  int i;

  if(m<=0) return;
  if(m>=n) return;
  i = m;

  while (0 < i && i < n) {
    if (dir == 1)
      i++;
    else
      i--;
  }
}
