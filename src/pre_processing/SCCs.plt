
:- module('SCCs_test',[]).

:-begin_tests('SCCs').

:-include('../search_paths.pl').
:-use_module('SCCs').
:-use_module('../utils/crs').
:-use_module(library(lambda)).


crs1([
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
	]).	
	
create_crse1(CRSE):-
	crse_empty(1,CRSE_empty),
	CRSE_empty=crse([],CRS_empty),
	crs1(Eqs),
	foldl(\Eq_l^CRS_l^CRS2_l^crs_add_eq(CRS_l,Eq_l,CRS2_l),Eqs,CRS_empty,CRS),
	CRSE=crse([entry(a(_),[])],CRS).	
	
test(compute_sccs_properties):-
	create_crse1(CRSE),
	compute_sccs_and_btcs(CRSE,SCCs,CRSE2),
	assertion(CRSE2==CRSE),
	assertion(SCCs=[
	scc(non_recursive,[e/1],[],[e/1],[]),
	scc(non_recursive,[d/1],[],[d/1],[]),
	scc(recursive,[c/1,c1/1,c2/1],[c/1-c1/1,c/1-c2/1,c1/1-c/1,c2/1-c/1],[c/1],[cover_points([c/1]),multiple]),
	scc(recursive,[b/1,b1/1,b2/1],[b/1-b1/1,b/1-b2/1,b1/1-b/1,b2/1-b1/1],[b/1],[cover_points([b/1]),non_tail,multiple]),
	scc(recursive,[a/1,a2/1],[a/1-a2/1,a2/1-a/1],[a/1],[cover_points([a/1]),non_tail])
	]).


crs2([
	eq(a(A),cost([],[],[],[],1),[a(A)],[]),
	eq(a(A),cost([],[],[],[],1),[b(A)],[]),
	eq(b(A),cost([],[],[],[],1),[a(A)],[]),
	eq(b(A),cost([],[],[],[],1),[b(A)],[])
	]).

create_crse2(CRSE):-
	crse_empty(1,CRSE_empty),
	CRSE_empty=crse([],CRS_empty),
	crs2(Eqs),
	foldl(\Eq_l^CRS_l^CRS2_l^crs_add_eq(CRS_l,Eq_l,CRS2_l),Eqs,CRS_empty,CRS),
	CRSE=crse([entry(a(_),[])],CRS).
		
test(compute_sccs_merge):-
	create_crse2(CRSE),
	compute_sccs_and_btcs(CRSE,SCCs,CRSE2),
	CRSE2=crse(_,CRS),
	assertion(crs_get_names(CRS,[ba/1])),
	assertion(SCCs=[scc(recursive,[ba/1],[ba/1-ba/1],[ba/1],[cover_points([ba/1])])]).
	
% multiple entries and irreducible

 %   scc_get_internal_callers/3,
  %  scc_get_cover_points/2


:-end_tests('SCCs').
