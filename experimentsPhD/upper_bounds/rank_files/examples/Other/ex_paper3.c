int *nondet;
void tick(int c);

void ex_paper3(int x,int y, int z){
 while(x>0) {
   if(nondet[x]){
     while(nondet[y] && y>0 ){
        y--;   
        tick(2);
     }
   }else{
   if(nondet[y])
       y++;
   else
       y=z;
   }
  x--;
 }

}
