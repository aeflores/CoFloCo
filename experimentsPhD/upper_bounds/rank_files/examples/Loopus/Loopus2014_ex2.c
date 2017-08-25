int nondet();

void Loopus2014_ex2(int m){
int i=m;
int n = 0;   
	while (i > 0){
	i--;
	if (nondet())  //push
		n++;        //stack.push(element);
	else    //popMany
	while (n > 0 && nondet())
		n--;    //element = stack.pop();
	}
}
