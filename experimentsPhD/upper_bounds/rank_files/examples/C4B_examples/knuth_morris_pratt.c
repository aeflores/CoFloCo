/* Knuth-Morris-Pratt string searching */
#include "assert.h"

int knuth_morris_pratt(int t[], int n, int p[], int m, int b[])
{
  int i = 0, j = 0, k = -1;

  while (i < n)
  {
    while (j >= 0 && t[i] != p[j]) {
       k = b[j];
       if(k <=0) return 0;
       if(k > j+1) return 0;
       j -= k;
    }
    i++, j++;
    if (j == m)
        break;
  }
  return i;
}

