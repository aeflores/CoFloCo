
:- module(partial_evaluation_test,[]).

:-begin_tests(partial_evaluation).

:-include('../search_paths.pl').
:-use_module('partial_evaluation').
:-use_module('SCCs',[compute_sccs_and_btcs/3]).
:-use_module('../utils/crs').
:-use_module('../utils/crs.plt',[create_crse/2]).
:-use_module(stdlib(numeric_abstract_domains),[nad_equals/2]).

crs_test:crse_example(crse_pe,[
	eq(a(A),cost([],[],[],[],1),[a(A)],[]),
	eq(a(A),cost([],[],[],[],1),[c(A),d(A)],[ 1*A>=1 ]),
	
	eq(c(A),cost([],[],[],[],1),[e(A),e(A)],[]),
	
	eq(d(A),cost([],[],[],[],1),[f(A)],[]),
	eq(d(A),cost([],[],[],[],1),[g(A)],[]),
	eq(d(A),cost([],[],[],[],1),[h(A)],[]),
	
	eq(e(A),cost([],[],[],[],1),[a(A)],[]),
	eq(e(A),cost([],[],[],[],2),[a(A)],[]),
	
	eq(f(A),cost([],[],[],[],1),[],[A=0]),
	eq(g(A),cost([],[],[],[],1),[],[]),
	eq(h(A),cost([],[],[],[],1),[],[])
	],[entry(a(A),[])]).	


test(pe_simple):-
	create_crse(crse_pe,CRSE),
	compute_sccs_and_btcs(CRSE,SCCs,CRSE2),
	partial_evaluation(CRSE2,SCCs,Ignored_set,CRSE3),
	assertion(Ignored_set=[]),
	CRSE3=crse(_,CRS2),
	crs_get_cr(CRS2,a,CR_a),
	cr_get_ceList(CR_a,Eqs_a),	
	assertion(Eqs_a=	[
				eq_ref(a(A),cost([],[],[],[],1),[],[a(A)],[a(A)],[],[]),
				eq_ref(a(A),cost([],[],[],[],4),[d(A)],[a(A),a(A)],[a(A),a(A),d(A)],[ 1*A>=1],[]),
				eq_ref(a(A),cost([],[],[],[],5),[d(A)],[a(A),a(A)],[a(A),a(A),d(A)],[ 1*A>=1],[]),
				eq_ref(a(A),cost([],[],[],[],6),[d(A)],[a(A),a(A)],[a(A),a(A),d(A)],[ 1*A>=1],[])
				]),
	assertion(crs_get_names(CRS2,[a/1,d/1])),
	crs_get_cr(CRS2,d,CR_d),
	cr_get_ceList(CR_d,Eqs_d),	
	% all the equations turn out to be equivalent or stronger
	assertion(Eqs_d=[
				eq_ref(d(A),cost([],[],[],[],2),[],[],[],[],[])
				]).
				
crs_test:crse_example(crse_pe2,[
	eq(a(A),cost([],[],[],[],1),[a(A)],[]),
	eq(a(A),cost([],[],[],[],1),[c(A),d(A)],[ 1*A>=1 ]),
	
	eq(c(A),cost([],[],[],[],1),[e(A)],[]),
	
	eq(e(A),cost([],[],[],[],1),[a(A)],[A=0]),
	eq(e(A),cost([],[],[],[],10),[a(A)],[]),
	
	eq(d(A),cost([],[],[],[],1),[f(A)],[]),
	eq(d(A),cost([],[],[],[],1),[g(A2)],[A2=A+1]),
	
	eq(f(A),cost([],[],[],[],1),[g(A)],[A=0]),
	eq(g(A),cost([],[],[],[],1),[h(A2)],[A2=A+1]),
	eq(h(A),cost([bound(ub,A,[iv1])],[],[],[(iv1,1)],0),[],[])
	],[entry(a(A),[])]).

test(pe_discard_and_increment):-
	create_crse(crse_pe2,CRSE),
	compute_sccs_and_btcs(CRSE,SCCs,CRSE2),
	partial_evaluation(CRSE2,SCCs,Ignored_set,CRSE3),
	assertion(Ignored_set=[]),
	CRSE3=crse(_,CRS2),
	crs_get_cr(CRS2,a,CR_a),
	cr_get_ceList(CR_a,Eqs_a),	
	assertion(Eqs_a=	[
				eq_ref(a(A),cost([],[],[],[],1),[],[a(A)],[a(A)],[],[]),
				eq_ref(a(A),cost([],[],[],[],12),[d(A)],[a(A)],[a(A),d(A)],[ 1*A>=1],[])
				]),
	assertion(crs_get_names(CRS2,[a/1,d/1])),
	crs_get_cr(CRS2,d,CR_d),
	cr_get_ceList(CR_d,Eqs_d),	
	% all the equations turn out to be equivalent or stronger
	assertion(Eqs_d=[
				eq_ref(d(A),cost([bound(ub,A2,[iv1])],[],[],[(iv1,1)],3),[],[],[],_,[]),
				eq_ref(d(A),cost([bound(ub,A2,[iv1])],[],[],[(iv1,1)],2),[],[],[],_,[])
				]),
	Eqs_d=[eq_ref(d(A),cost([bound(ub,A2,[iv1])],[],[],[(iv1,1)],3),[],[],[],Cs1,[]),
		   eq_ref(d(A),cost([bound(ub,A2,[iv1])],[],[],[(iv1,1)],2),[],[],[],Cs2,[])
		   ],
	assertion(nad_equals(Cs1,[A2=A+1,A=0])),
	assertion(nad_equals(Cs2,[A2=A+2])).
	

:-end_tests(partial_evaluation).
