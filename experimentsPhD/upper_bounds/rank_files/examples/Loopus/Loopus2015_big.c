int nondet();
void tick(int c);

void Loopus2015_big(int len) {
int beg=0;int end=0;int i = 0;
int k;
 while(i < len) {
	i++;
	if (nondet())
		end = i;
	if (nondet()) {
		k = beg;
		while (k < end){
            tick(1);
			k++;
        }
		end = i;
		beg = end;
	} else if(nondet()) {
		end = i;
		beg = end;
	}
 }
}
