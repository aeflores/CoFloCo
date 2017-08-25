#include "assert.h"

void speed_pldi09_fig4_4(int n, int m)
{
  int i=n;

  if(m<=0) return;

  while (i > 0) {
    if (i < m)
      i=i-1;
    else
      i=i-m;
  }
}
