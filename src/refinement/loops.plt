

	
:-begin_tests(loops).
:-include('../search_paths.pl').
:-use_module('loops').
:-use_module('../utils/crs').
:-use_module('../utils/crs.plt',[create_crse/2]).
:-use_module(stdlib(numeric_abstract_domains),[nad_equals/2]).

crs_test:crse_example(crse_loops1,[
	eq_ref(a(A),cost([],[],[],[],1),[],[],[],[A=A2],[terminating]),
	eq_ref(a(A),cost([],[],[],[],1),[d(B)],[a(A2)],[a(A2),d(B)],[ 1*A>=1,A2=A+1,B=A+1 ],[terminating]),
	eq_ref(a(A),cost([],[],[],[],1),[c(B)],[a(A2)],[a(A2),c(B)],[ 1*A>=1,A2=A+1,B=A+10 ],[terminating]),
	eq_ref(a(A),cost([],[],[],[],1),[c(B)],[a(A2)],[a(A2),c(B)],[ 1*A>=0,A2=A+1,B=A+11 ],[terminating])
	],[entry(a(A),[])]).	

	
test(no_compress):-
	create_crse(crse_loops1,CRSE),
	CRSE=crse(_,CRS),
	crs_get_cr(CRS,a,CR),
	compute_loops(CR,0,CR2),
	cr_get_loops(CR2,Loops),
	
	Loops=loops(range(1,5),[
	(1,loop(a(A),[],Inv1,[eqs([1]),terminating])),
	(2,loop(a(A),[a(A2)],Inv3,[eqs([3]),terminating])),
	(3,loop(a(A),[a(A2)],Inv2,[eqs([2]),terminating])),
	(4,loop(a(A),[a(A2)],Inv4,[eqs([4]),terminating]))]),
	assertion(nad_equals(Inv1,[])),
	assertion(nad_equals(Inv2,[1*A>=1,A2=A+1])),
	assertion(nad_equals(Inv3,[1*A>=1,A2=A+1])),
	assertion(nad_equals(Inv4,[1*A>=0,A2=A+1])).

test(compress_yes):-
	create_crse(crse_loops1,CRSE),
	CRSE=crse(_,CRS),
	crs_get_cr(CRS,a,CR),
	compute_loops(CR,1,CR2),
	cr_get_loops(CR2,Loops),
	
	Loops=loops(range(1,4),[
	(1,loop(a(A),[],Inv1,[eqs([1]),terminating])),
	(2,loop(a(A),[a(A2)],Inv2,[eqs([2,3]),terminating])),
	(3,loop(a(A),[a(A2)],Inv3,[eqs([4]),terminating]))]),
	assertion(nad_equals(Inv1,[])),
	assertion(nad_equals(Inv2,[1*A>=1,A2=A+1])),
	assertion(nad_equals(Inv3,[1*A>=0,A2=A+1])).	
	
test(compress2):-
	create_crse(crse_loops1,CRSE),
	CRSE=crse(_,CRS),
	crs_get_cr(CRS,a,CR),
	compute_loops(CR,2,CR2),
	cr_get_loops(CR2,Loops),
	
	Loops=loops(range(1,3),[
	(1,loop(a(A),[],Inv1,[eqs([1]),terminating])),
	(2,loop(a(A),[a(A2)],Inv2,[eqs([2,3,4]),terminating]))]),
	assertion(nad_equals(Inv1,[])),
	assertion(nad_equals(Inv2,[1*A>=0,A2=A+1])).		

	
crs_test:crse_example(crse_loops2,[
	eq_ref(a(A),cost([],[],[],[],1),[],[],[],[A=A2],[terminating]),
	eq_ref(a(A),cost([],[],[],[],1),[d(B)],[a(A2)],[a(A2),d(B)],[ 1*A>=1,A2=A+1,B=A+1 ],[terminating]),
	eq_ref(a(A),cost([],[],[],[],1),[c(B)],[a(A2)],[a(A2),c(B)],[ 1*A>=1,A2=A+1,B=A+10 ],[terminating]),
	eq_ref(a(A),cost([],[],[],[],1),[c(B)],[a(A2)],[a(A2),c(B)],[ 1*A>=0,A2=A+1,B=A+11 ],[non_terminating])
	],[entry(a(A),[])]).	
		
test(compress_info):-
	create_crse(crse_loops2,CRSE),
	CRSE=crse(_,CRS),
	crs_get_cr(CRS,a,CR),
	compute_loops(CR,2,CR2),
	cr_get_loops(CR2,Loops),
	Loops=loops(range(1,4),[
	(1,loop(a(A),[],Inv1,[eqs([1]),terminating])),
	(2,loop(a(A),[a(A2)],Inv3,[eqs([4]),non_terminating])),
	(3,loop(a(A),[a(A2)],Inv2,[eqs([2,3]),terminating]))
	]),
	assertion(nad_equals(Inv1,[])),
	assertion(nad_equals(Inv2,[1*A>=1,A2=A+1])),
	assertion(nad_equals(Inv3,[1*A>=0,A2=A+1])).	

:-end_tests(loops).
