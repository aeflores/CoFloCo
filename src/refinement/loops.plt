

	
:-begin_tests(loops).
:-include('../search_paths.pl').
:-use_module('loops').
:-use_module('../utils/crs').
:-use_module('../utils/crs.plt',[create_crse/2]).
:-use_module(stdlib(numeric_abstract_domains),[nad_equals/2]).

crs_test:crse_example(crse_loops1,[
	eq_ref(a(A),cost([],[],[],[],1),[],[],[],[A=A2],[(termination,terminating)]),
	eq_ref(a(A),cost([],[],[],[],1),[d(B)],[a(A2)],[a(A2),d(B)],[ 1*A>=1,A2=A+1,B=A+1 ],[(termination,terminating)]),
	eq_ref(a(A),cost([],[],[],[],1),[c(B)],[a(A2)],[a(A2),c(B)],[ 1*A>=1,A2=A+1,B=A+10 ],[(termination,terminating)]),
	eq_ref(a(A),cost([],[],[],[],1),[c(B)],[a(A2)],[a(A2),c(B)],[ 1*A>=0,A2=A+1,B=A+11 ],[(termination,terminating)])
	],[entry(a(A),[])]).	

	
test(no_compress):-
	create_crse(crse_loops1,CRSE),
	CRSE=crse(_,CRS),
	crs_get_cr(CRS,a,CR),
	compute_loops(CR,0,Loops),
	
	Loops=loops(range(1,5),[
	(1,loop(a(A),[],Inv1,[(eqs,eqs([1])),(ioVars,ioVars(a(A),[A],[])),(termination,terminating)])),
	(2,loop(a(A),[a(A2)],Inv3,[(eqs,eqs([3])),(ioVars,ioVars(a(A),[A],[])),(termination,terminating)])),
	(3,loop(a(A),[a(A2)],Inv2,[(eqs,eqs([2])),(ioVars,ioVars(a(A),[A],[])),(termination,terminating)])),
	(4,loop(a(A),[a(A2)],Inv4,[(eqs,eqs([4])),(ioVars,ioVars(a(A),[A],[])),(termination,terminating)]))
	]),
	assertion(nad_equals(Inv1,[])),
	assertion(nad_equals(Inv2,[1*A>=1,A2=A+1])),
	assertion(nad_equals(Inv3,[1*A>=1,A2=A+1])),
	assertion(nad_equals(Inv4,[1*A>=0,A2=A+1])),
	
	loops_get_head(Loops,Head),
	assertion(Head=a(A)),
	loops_get_list(Loops,List_loops),
	assertion(List_loops=[
	loop(a(A),[],Inv1,[(eqs,eqs([1])),(ioVars,ioVars(a(A),[A],[])),(termination,terminating)]),
	loop(a(A),[a(A2)],Inv3,[(eqs,eqs([3])),(ioVars,ioVars(a(A),[A],[])),(termination,terminating)]),
	loop(a(A),[a(A2)],Inv2,[(eqs,eqs([2])),(ioVars,ioVars(a(A),[A],[])),(termination,terminating)]),
	loop(a(A),[a(A2)],Inv4,[(eqs,eqs([4])),(ioVars,ioVars(a(A),[A],[])),(termination,terminating)])]),
	
	assertion(loop_get_CEs(loop(a(A),[a(A2)],Inv3,[(eqs,eqs([3])),(termination,terminating)]),[3])).

test(compress_yes):-
	create_crse(crse_loops1,CRSE),
	CRSE=crse(_,CRS),
	crs_get_cr(CRS,a,CR),
	compute_loops(CR,1,Loops),
	
	Loops=loops(range(1,4),[
	(1,loop(a(A),[],Inv1,[(eqs,eqs([1])),(ioVars,ioVars(a(A),[A],[])),(termination,terminating)])),
	(2,loop(a(A),[a(A2)],Inv2,[(eqs,eqs([2,3])),(ioVars,ioVars(a(A),[A],[])),(termination,terminating)])),
	(3,loop(a(A),[a(A2)],Inv3,[(eqs,eqs([4])),(ioVars,ioVars(a(A),[A],[])),(termination,terminating)]))]),
	assertion(nad_equals(Inv1,[])),
	assertion(nad_equals(Inv2,[1*A>=1,A2=A+1])),
	assertion(nad_equals(Inv3,[1*A>=0,A2=A+1])).	
	
test(compress2):-
	create_crse(crse_loops1,CRSE),
	CRSE=crse(_,CRS),
	crs_get_cr(CRS,a,CR),
	compute_loops(CR,2,Loops),
	
	Loops=loops(range(1,3),[
	(1,loop(a(A),[],Inv1,[(eqs,eqs([1])),(ioVars,ioVars(a(A),[A],[])),(termination,terminating)])),
	(2,loop(a(A),[a(A2)],Inv2,[(eqs,eqs([2,3,4])),(ioVars,ioVars(a(A),[A],[])),(termination,terminating)]))]),
	assertion(nad_equals(Inv1,[])),
	assertion(nad_equals(Inv2,[1*A>=0,A2=A+1])).		

	
crs_test:crse_example(crse_loops2,[
	eq_ref(a(A),cost([],[],[],[],1),[],[],[],[A=A2],[(termination,terminating)]),
	eq_ref(a(A),cost([],[],[],[],1),[d(B)],[a(A2)],[a(A2),d(B)],[ 1*A>=1,A2=A+1,B=A+1 ],[(termination,terminating)]),
	eq_ref(a(A),cost([],[],[],[],1),[c(B)],[a(A2)],[a(A2),c(B)],[ 1*A>=1,A2=A+1,B=A+10 ],[(termination,terminating)]),
	eq_ref(a(A),cost([],[],[],[],1),[c(B)],[a(A2)],[a(A2),c(B)],[ 1*A>=0,A2=A+1,B=A+11 ],[(termination,non_terminating)])
	],[entry(a(A),[])]).	
		
test(compress_info):-
	create_crse(crse_loops2,CRSE),
	CRSE=crse(_,CRS),
	crs_get_cr(CRS,a,CR),
	compute_loops(CR,2,Loops),
	Loops=loops(range(1,4),[
	(1,loop(a(A),[],Inv1,[(eqs,eqs([1])),(ioVars,ioVars(a(A),[A],[])),(termination,terminating)])),
	(2,loop(a(A),[a(A2)],Inv3,[(eqs,eqs([4])),(ioVars,ioVars(a(A),[A],[])),(termination,non_terminating)])),
	(3,loop(a(A),[a(A2)],Inv2,[(eqs,eqs([2,3])),(ioVars,ioVars(a(A),[A],[])),(termination,terminating)]))
	]),
	assertion(nad_equals(Inv1,[])),
	assertion(nad_equals(Inv2,[1*A>=1,A2=A+1])),
	assertion(nad_equals(Inv3,[1*A>=0,A2=A+1])).
	
	
loops_example(ex1,Loops):-
	Loops=loops(_,[
	       (1,loop(a(A),[],[A=0],[])),
	       (2,loop(a(A),[a(A2)],[A>=0,A2=A-1],[])),
	       (3,loop(a(A),[a(A2)],[A>=1,A2=A-1],[])),
	       (4,loop(a(A),[a(A2)],[A>=1,A2=A-2],[])),
	       (5,loop(a(A),[a(A2),a(A3)],[A>=1,A2=A-1,A3=A-2],[]))]).
	       
test(phase_loops):-
	loops_example(ex1,Loops),
	compute_phase_loops(Loops,chains([phase(5,[]),phase([3,4],[]),phase([2],[]),phase(1,[])],_),chains(Annotated_phases1,_)),
	compute_phase_loops(Loops,chains([phase([2,3,4],[])],_),chains(Annotated_phases2,_)),
	compute_phase_loops(Loops,chains([phase([2,5],[])],_),chains(Annotated_phases3,_)),
	Annotated_phases1=[
	phase(5,[(phase_loop,phase_loop(Head,Call,Cs1))]),
	phase([3,4],[(phase_loop,phase_loop(Head,Call,Cs2))]),
	phase([2],[(phase_loop,phase_loop(Head,Call,Cs3))]),
	phase(1,[(phase_loop,phase_loop(Head,none,Cs4))])],
	Head=a(X),Call=a(X2),
	assertion(nad_equals(Cs1,[X>=1,X2=<X-1,X2>=X-2])),
	assertion(nad_equals(Cs2,[X>=1,X2=<X-1,X2>=X-2])),
	assertion(nad_equals(Cs3,[X>=0,X2=X-1])),
	assertion(nad_equals(Cs4,[X=0])),
	
	Annotated_phases2=[phase([2,3,4],[(phase_loop,phase_loop(Head,Call,Cs5))])],
	assertion(nad_equals(Cs5,[X2+1>=0,X2=<X-1,X2>=X-2])),
	Annotated_phases3=[phase([2,5],[(phase_loop,phase_loop(Head,Call,Cs6))])],
	assertion(nad_equals(Cs6,[X2+1>=0,X2=<X-1,X2>=X-2])).    
	       

test(strengthen_loops):-
	loops_example(ex1,Loops),
	Loop_invs=loop_invs(a(Ap),[
		(1,[]),
		(3,[Ap=0]),
		(4,[Ap=<10]),
		(5,[Ap=<10])
		]),
	loops_strengthen_with_loop_invs(Loops,head,Loop_invs,Loops2,Discarded),
	assertion(Discarded=[2,3]),
	
	loops_get_loop(Loops2,4,Loop4),
	loop_head(Loop4,a(A)),
	loop_calls(Loop4,[a(A2)]),
	loop_constraints(Loop4,Cs4),
	assertion(nad_equals(Cs4,[A>=1,A2=A-2,A=<10])),
	
	
	loops_get_loop(Loops2,5,Loop5),
	loop_head(Loop5,a(A)),
	loop_calls(Loop5,[a(A2),a(A3)]),
	loop_constraints(Loop5,Cs5),
	assertion(nad_equals(Cs5,[A>=1,A2=A-1,A3=A-2,A=<10])).
	

test(strengthen_loops_call):-
	loops_example(ex1,Loops),
	Loop_invs=loop_invs(a(Ap),[
		(1,[]),
		(3,[Ap+1=<0]),
		(4,[Ap=<10]),
		(5,[Ap=<10])
		]),
	loops_strengthen_with_loop_invs(Loops,call,Loop_invs,Loops2,Discarded),
	assertion(Discarded=[2,3]),
	
	loops_get_loop(Loops2,4,Loop4),
	loop_head(Loop4,a(A)),
	loop_calls(Loop4,[a(A2)]),
	loop_constraints(Loop4,Cs4),
	assertion(nad_equals(Cs4,[A>=1,A2=A-2,A2=<10])),
	
	
	loops_get_loop(Loops2,5,Loop5),
	loop_head(Loop5,a(A)),
	loop_calls(Loop5,[a(A2),a(A3)]),
	loop_constraints(Loop5,Cs5),
	assertion(nad_equals(Cs5,[A>=1,A2=A-1,A3=A-2,A2=<10,A3=<10])).	
	
:-end_tests(loops).
