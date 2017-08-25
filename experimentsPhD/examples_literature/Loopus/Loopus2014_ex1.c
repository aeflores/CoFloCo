int nondet();
void tick(int cost);

void Loopus2014_ex1(int n){
int a = n, b = 0;
while (a > 0){
	a--; b++;
	while (b > 0){
		b--;tick(1);
		for (int i = n-1; i > 0; i--)
			if (a > 0 && nondet()>0){
				a--; b++;
			}  
		} 
	 }
}
