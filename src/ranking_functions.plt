:- module(ranking_functions_test,[
		
	]).

	
:-begin_tests(ranking_functions).


:-use_module(ranking_functions).
:-use_module('refinement/loops').
:-use_module('refinement/chains').
	

	
test(ranking_loops):-
	Loops=loops(range(1,5),[
	(1,loop(a(A,B,C),[],[A>=1],[])), % no rfs
	(2,loop(a(A,B,C),[a(A2,B2,C2)],[A2=A-1,A>=1],[])),% 1 rf
	(3,loop(a(A,B,C),[a(A2,B2,C2)],[A2=A+1,A=<B,B2=B],[])),%1 rf b-a
	(4,loop(a(A,B,C),[a(A2,B2,C2),a(A3,B3,C3)],[A2+A3=A-1,A2>=0,A3>=0,B2=B-1,B>=3,B3=B,C3=C-1,C>=1],[])),% [a,b-2] and [a] for each sub-loop
	(5,loop(a(A,B,C),[a(A2,B2,C2)],[A2=A-2,A>=1,B2=B-3,B>=1,C2=C-1,C>=1],[])) % 2 rf with fractions because of the input vars
	]),
	find_loops_ranking_functions(ioVars(a(A,B,C),[A,B],[C]),Loops,Loops2),
	 %non recursion
	 loops_get_loop_fresh(Loops2,1,Loop1),
	 loop_head(Loop1,a(a,b,c)),
	 loop_get_property(Loop1,ranking_functions,ranking_functions(Rf1)),
	 assertion(ground(Rf1)),
	 assertion(Rf1=[]),

	 loops_get_loop_fresh(Loops2,2,Loop2),
	 loop_head(Loop2,a(a,b,c)),
	 loop_get_property(Loop2,ranking_functions,ranking_functions(Rf2)),
	 assertion(ground(Rf1)),
	 assertion(Rf2=[(1,[1*a])]),
	 
	 loops_get_loop_fresh(Loops2,3,Loop3),
	 loop_head(Loop3,a(a,b,c)),
	 loop_get_property(Loop3,ranking_functions,ranking_functions(Rf3)),
	 assertion(ground(Rf3)),
	 assertion(Rf3=[(1,[-1*a+1*b+1])]),
	 
	 %multiple recursion and offsets
	 loops_get_loop_fresh(Loops2,4,Loop4),
	 loop_head(Loop4,a(a,b,c)),
	 loop_get_property(Loop4,ranking_functions,ranking_functions(Rf4)),
	 assertion(ground(Rf4)),
	 assertion(Rf4=[(1,[1*a,1*b+(-2)]),(2,[1*a])]),
	 
	 %fractions
	 loops_get_loop_fresh(Loops2,5,Loop5),
	 loop_head(Loop5,a(a,b,c)),
	 loop_get_property(Loop5,ranking_functions,ranking_functions(Rf5)),
	 assertion(ground(Rf5)),
	 assertion(Rf5=[(1,[1/2*a,1/3*b])]).

test(prove_phases_termination):-
		Loops=loops(range(1,5),[
	(1,loop(a(A,B,C),[a(A2,B2,C2)],[A2=A-1,A>=1,B2=B,       C2=C],[])),
	(2,loop(a(A,B,C),[a(A2,B2,C2)],[A2=A-2,A>=1,B2=B,       C2=C],[])),
	(3,loop(a(A,B,C),[a(A2,B2,C2)],[            B2=B-1,B>=1,C2=C],[])),
	(4,loop(a(A,B,C),[a(A2,B2,C2)],[                        C2=C-1,C>=1],[])) ,
	(5,loop(a(A,B,C),[a(A2,B2,C2)],[A2=A-1,A>=1,B2=B,C2=C+1],[])) 
	]),
	IoVars=ioVars(a(A,B,C),[A,B,C],[]),
	find_loops_ranking_functions(IoVars,Loops,Loops2),
	
	Chains=chains([phase([1,2],[]),phase([1,2,3,4],[]),phase([1,2,3,4,5],[])],[]),
	compute_phase_loops(Loops,Chains,Chains2),
	prove_phases_termination(Chains2,IoVars,Loops2,Chains3),
	
	Chains3=chains([Phase12,Phase1234,Phase12345],_),
	phase_get_property(Phase12,termination,Term235),
	assertion(Term235=terminating(a(a,b,c),[rf_covers(1*a,all)])),
	
	phase_get_property(Phase1234,termination,Term1234),
	assertion(Term1234=terminating(a(a,b,c),[rf_covers(1*a,[1:1,2:1]),rf_covers(1*b,[3:1]),rf_covers(1*c,[4:1])])),
	
	phase_get_property(Phase12345,termination,Term12345),
	assertion(Term12345=non_terminating(a(a,b,c),[not_covered([1:1,2:1,3:1,4:1,5:1])])).
	
test(prove_phases_termination_partial_cover):-
		Loops=loops(range(1,5),[
	(1,loop(a(A,B,C),[a(A2,B2,C2)],[A2=A-1,A>=1,B2=B,       C2=C],[])),
	(2,loop(a(A,B,C),[a(A2,B2,C2)],[A2=A-2,A>=1,B2=B,       C2=C],[])),
	(3,loop(a(A,B,C),[a(A2,B2,C2)],[A2=A,           B2=B-1,B>=1],[])),
	(4,loop(a(A,B,C),[a(A2,B2,C2)],[A2=A,                       C2=C-1,C>=1],[]))
	]),
	IoVars=ioVars(a(A,B,C),[A,B,C],[]),
	find_loops_ranking_functions(IoVars,Loops,Loops2),
	Chains=chains([phase([1,2,3,4],[])],[]),
	compute_phase_loops(Loops,Chains,Chains2),
	prove_phases_termination(Chains2,IoVars,Loops2,Chains3),
	Chains3=chains([Phase1234],_),	
	phase_get_property(Phase1234,termination,Term1234),
	assertion(Term1234=non_terminating(a(a,b,c),[not_covered([3:1,4:1]),rf_covers(1*a,[1:1,2:1])])).


test(prove_phases_termination_mutiplerec):-
		Loops=loops(range(1,3),[
	(1,loop(a(A,B,C),[a(A2,B2,C2),a(A3,B3,C3)],[A2=A-1,A>=1,  A3=A,B3=B-1,B>=1,      C2=C-1,C3=C-1,C>=1],[])),
	(2,loop(a(A,B,C),[a(A2,B2,C2),a(A3,B3,C3)],[A3=A-1,A>=1,  A2=A,B2=B-1,B>=1,      C2=C-1,C3=C-1,C>=1],[]))
	]),
	IoVars=ioVars(a(A,B,C),[A,B],[C]),
	find_loops_ranking_functions(IoVars,Loops,Loops2),
	Chains=chains([phase([1,2],[])],[]),
	compute_phase_loops(Loops,Chains,Chains2),
	prove_phases_termination(Chains2,IoVars,Loops2,Chains3),
	Chains3=chains([Phase12],_),	
	phase_get_property(Phase12,termination,Term12),
	assertion(Term12=terminating(a(a,b,c),[rf_covers(1*b,[1:2,2:1]),rf_covers(1*a,[1:1,2:2])])).


test(prove_phases_termination_no_rf):-
		Loops=loops(range(1,3),[
	(1,loop(a(A,B,C),[a(A2,B2,C2)],[A2=A-1,A>=1],[])),
	(2,loop(a(A,B,C),[a(A2,B2,C2)],[A2=A],[]))
	]),
	IoVars=ioVars(a(A,B,C),[A,B],[C]),
	find_loops_ranking_functions(IoVars,Loops,Loops2),
	Chains=chains([phase([1,2],[])],[]),
	compute_phase_loops(Loops,Chains,Chains2),
	prove_phases_termination(Chains2,IoVars,Loops2,Chains3),
	Chains3=chains([Phase12],_),	
	phase_get_property(Phase12,termination,Term12),
	assertion(Term12=non_terminating(a(a,b,c),[not_covered([2:1]),rf_covers(1*a,[1:1])])).
:-end_tests(ranking_functions).
