
:- module('SCCs_test',[]).

:-begin_tests('SCCs').

:-include('../search_paths.pl').
:-use_module('SCCs').
:-use_module('../utils/crs').
:-use_module('../utils/crs.plt',[create_crse/2]).
:-use_module(library(lambda)).


crs_test:crse_example(scc1,[
	eq(a(A),cost([],[],[],[],1),[],[ A=0 ]),
	eq(a(A),cost([],[],[],[],1),[a2(A),b(A)],[A>=1 ]),
	eq(a2(A),cost([],[],[],[],1),[a(A)],[A>=1 ]),
	
	eq(b(A),cost([],[],[],[],1),[],[ A=0 ]),
	eq(b(A),cost([],[],[],[],1),[b1(A),b2(A),c(A)],[]),
	eq(b1(A),cost([],[],[],[],1),[b(A)],[]),
	eq(b2(A),cost([],[],[],[],1),[b1(A)],[]),
	
	eq(c(A),cost([],[],[],[],1),[],[ A=0 ]),
	eq(c(A),cost([],[],[],[],1),[d(A),c1(A),c2(A)],[]),
	eq(c1(A),cost([],[],[],[],1),[c(A)],[]),
	eq(c2(A),cost([],[],[],[],1),[c(A)],[]),
	
	eq(d(A),cost([],[],[],[],1),[e(A)],[]),

	eq(e(A),cost([],[],[],[],1),[],[])
	],[entry(a(_),[])]).	

crs_test:crse_example(scc2,[
	eq(a(A),cost([],[],[],[],1),[a(A)],[]),
	eq(a(A),cost([],[],[],[],1),[b(A)],[]),
	eq(b(A),cost([],[],[],[],1),[a(A)],[]),
	eq(b(A),cost([],[],[],[],1),[b(A)],[])
	],[entry(a(_),[])]).


crs_test:crse_example(scc3,[
	eq(e(A),cost([],[],[],[],1),[a(A)],[]),
	eq(e(A),cost([],[],[],[],1),[b(A)],[]),
	
	eq(a(A),cost([],[],[],[],1),[a(A)],[]),
	eq(a(A),cost([],[],[],[],1),[b(A)],[]),
	eq(b(A),cost([],[],[],[],1),[a(A)],[]),
	eq(b(A),cost([],[],[],[],1),[b(A)],[])
	],[entry(e(_),[])]).
	

	
	
	
test(compute_sccs_properties):-
	create_crse(scc1,CRSE),
	compute_sccs_and_btcs(CRSE,SCCs,CRSE2),
	assertion(CRSE2==CRSE),
	assertion(SCCs=[
	scc(non_recursive,[e/1],[],[e/1],[]),
	scc(non_recursive,[d/1],[],[d/1],[]),
	scc(recursive,[c/1,c1/1,c2/1],[c/1-c1/1,c/1-c2/1,c1/1-c/1,c2/1-c/1],[c/1],[cover_points([c/1]),multiple]),
	scc(recursive,[b/1,b1/1,b2/1],[b/1-b1/1,b/1-b2/1,b1/1-b/1,b2/1-b1/1],[b/1],[cover_points([b/1]),non_tail,multiple]),
	scc(recursive,[a/1,a2/1],[a/1-a2/1,a2/1-a/1],[a/1],[cover_points([a/1]),non_tail])
	]).

test(compute_sccs_merge):-
	create_crse(scc2,CRSE),
	compute_sccs_and_btcs(CRSE,SCCs,CRSE2),
	CRSE2=crse(_,CRS),
	assertion(crs_get_names(CRS,[ba/1])),
	assertion(SCCs=[scc(recursive,[ba/1],[ba/1-ba/1],[ba/1],[cover_points([ba/1])])]).
	
test(compute_sccs_merge_multiple_entries):-
	create_crse(scc3,CRSE),
	compute_sccs_and_btcs(CRSE,SCCs,CRSE2),
	CRSE2=crse(_,CRS),
	assertion(crs_get_names(CRS,[ab/1,e/1])),
	assertion(SCCs=[scc(recursive,[ab/1],[ab/1-ab/1],[ab/1],[cover_points([ab/1])]),scc(non_recursive,[e/1],[],[e/1],[cover_points([e/1])])]).
	
% multiple entries and irreducible

 %   scc_get_internal_callers/3,
  %  scc_get_cover_points/2


:-end_tests('SCCs').
