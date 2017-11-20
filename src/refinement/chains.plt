
	
:-begin_tests(chains).

:-use_module(chains).

loops_example(sequence,
	loops(range(1,6),[
	(1,loop(a(A),[],[],[])),
	(2,loop(a(A),[],[A=20],[])),
	(3,loop(a(A),[a(A2)],[1*A=10,A2=A+1],[])),
	(4,loop(a(A),[a(A2)],[1*A>=11,A2=A+1],[])),
	(5,loop(a(A),[a(A2)],[1*A=<9,A2=A+1],[]))
	])).
		
loops_example(alternative,
	loops(range(1,4),[
	(1,loop(a(A),[],[A=0],[])),
	(2,loop(a(A),[a(A2)],[1*A>=1,A2=A-1],[])),
	(3,loop(a(A),[a(A2)],[1*A+1=<0,A2=A+1],[]))
	])).

loops_example(all_possible,
	loops(range(1,4),[
	(1,loop(a(A,B,C),[],[A=0],[])),
	(2,loop(a(A,B,C),[a(A,B,C)],[A=1],[])),
	(3,loop(a(A,B,C),[a(A,B,C)],[B=1],[])),
	(4,loop(a(A,B,C),[a(A,B,C)],[C=1],[]))
	])).
	
loops_example(multiple,
	loops(range(1,4),[
	(1,loop(a(A),[],[A=0],[])),
	(2,loop(a(A),[a(A2),a(A2)],[A=1,A2=A-1],[])),
	(3,loop(a(A),[a(A2),a(A2)],[A>=1,A2=A-1],[])),
	(4,loop(a(A),[a(A)],[A>=10,A2=A-1],[]))
	])).
		
test(chains_sequence):-
	loops_example(sequence,Loops),
	compute_chains(Loops,chains(Phases,Chains)),
	assertion(Phases=[[5],3,[4],2,1]),
	assertion(Chains=[
	[1],
	[2],
	
	[3,1],
	[3,[4]],
	[3,[4],1],
	[3,[4],2],
	
		
	[[4]],
	[[4],1],
	[[4],2],
	
	
	[[5]],
	[[5],1],
	[[5],3,1],
	[[5],3,[4]],
	[[5],3,[4],1],
	[[5],3,[4],2]	
	]).

	
test(chains_alternative):-
	loops_example(alternative,Loops),
	compute_chains(Loops,chains(Phases,Chains)),
	assertion(Phases=[[3],[2],1]),
	assertion(Chains=[
	[1],
	[[2]],
    [[2],1],
  
    [[3]],
    [[3],1]
	]).	
	
	
	
test(chains_all_possible):-
	loops_example(all_possible,Loops),
	compute_chains(Loops,chains(Phases,Chains)),
	assertion(Phases=[[2,3,4],1]),
	assertion(Chains=[
	[1],
	[[2,3,4]],
    [[2,3,4],1]
	]).	
test(chains_multiple):-
	loops_example(multiple,Loops),
	compute_chains(Loops,chains(Phases,Chains)),
	assertion(Phases=[[3,4],2,1]),
	assertion(Chains=[
	[1],
	[multiple(2,[[1]])],
	[multiple([3,4],[[],[1],[multiple(2,[[1]])]])]
	]).		

:-end_tests(chains).