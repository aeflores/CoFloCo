int nondet();

void start(int m){
int i=m, n = 0;   //stack = emptyStack();
	while (i > 0){
	i--;
	if (nondet()>0)  //push
		n++;        //stack.push(element);
	else    //popMany
	while (n > 0 && nondet()>0)
		n--;    //element = stack.pop();
	}
}
