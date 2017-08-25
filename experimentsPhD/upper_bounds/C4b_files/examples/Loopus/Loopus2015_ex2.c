#include "assert.h"

int nondet();

void foo(int n, int m1,int m2) {
 assert(n>=0);
 assert(m1>=0);
 assert(m2>=0);
 int y = n;
 int x;
 if(nondet()>0)
    x = m1;
 else
  x = m2;
 while(y > 0) {
   y--;
   x = x + 2; 
  }
 int z = x;
  while(z > 0)
   z--; 
}



