#include "assert.h"

int nondet();

void Loopus2015_ex2(int n, int m1,int m2) {
 int y = n;
 int x;
 int z;
 if (n<0) return;
 if (m1<0) return;
 if (m2<0) return;


 if(nondet()>0)
    x = m1;
 else
  x = m2;
 while(y > 0) {
   y--;
   x = x + 2; 
  }
 z = x;
  while(z > 0)
   z--; 
}



