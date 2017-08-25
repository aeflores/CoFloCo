#include "assert.h"
int nondet();
void tick(int cost);

void start(int l, int h) {
  assert(l < h);
  for (;;) {
    do { l++; tick(1); } while (l<h && nondet()>0);
    do { h--; tick(1); } while (l<h && nondet()>0);
    if (l >= h) break;
    tick(1);
  }
}

