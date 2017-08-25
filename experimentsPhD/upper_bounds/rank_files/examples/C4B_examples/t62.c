#include "assert.h"
int nondet();
void tick(int cost);

void t62(int l, int h) {
  if(l>=h) return;
  while(1) {
    do { l++; tick(1); } while (l<h && nondet()>0);
    do { h--; tick(1); } while (l<h && nondet()>0);
    if (l >= h) break;
    tick(1);
  }
}

