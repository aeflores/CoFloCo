

int nondet();

void foo(int n) {
 int x = n;
 int r = 0;
 while(x > 0) {
  x = x - 1;
  r = r + 1;
  if(nondet()>0) {
   int p = r;
   while(p > 0)
     p--;
   r = 0;
  }
 } 
}


