:- module(unfolding_test,[
		
	]).

	
:-begin_tests(unfolding).


:-use_module(unfolding).
:-use_module(loops,[compute_loops/3]).
:-use_module(invariants,[compute_backward_invariants/3]).
:-use_module(chains,[compute_chains/3,chains_annotate_termination/3]).

:-use_module('../utils/crs').
:-use_module('../utils/crs.plt',[create_crse/2]).
:-use_module(stdlib(numeric_abstract_domains),[nad_equals/2]).


crs_test:crse_example(crse_unfold2,[
	eq_ref(a(A),cost([],[],[],[],1),[],[],[],[],[]),
	eq_ref(a(A),cost([],[],[],[],1),[dec_pos(A,B)],[a(B)],[dec_pos(A,B),a(B)],[ A>=0 ],[]),
	eq_ref(a(A),cost([],[],[],[],1),[dec_pos(A,B),dec_pos(B,C)],[a(C)],[dec_pos(A,B),dec_pos(B,C),a(C)],[ A>=1 ],[]),
	
	eq_ref(dec_pos(A,B),cost([],[],[],[],1),[],[],[],[A>=1,B=A-1],[]),
	eq_ref(dec_pos(A,B),cost([],[],[],[],1),[],[],[],[A=<0,B=A],[])

	],[entry(a(A),[])]).	

test(simple_unfold):-
	create_crse(crse_unfold2,CRSE),	
	CRSE=crse(_,CRS),
	crs_get_cr(CRS,a,CRa),
	crs_get_cr(CRS,dec_pos,CRdec),
	External_patts=external_patterns(dec_pos(Ap,Bp),[
		(1,external_pattern([termination(terminating),summary([Ap>=1,Bp=Ap-1])])),
		(2,external_pattern([termination(terminating),summary([Ap=<0,Bp=Ap])]))
		]),
	cr_set_external_patterns(CRdec,External_patts,CRdec2),
	crs_update_cr(CRS,dec_pos,CRdec2,CRS2),
	cr_specialize(CRa,CRS2,CRa2),
	
	cr_get_ceList_with_id(CRa2,ListEqs),
	ListEqs=
		[
		(6,eq_ref(a(A),cost([],[],[],[],1),[],[],[],[],[(refined,refined(1)),(termination,terminating)])),

		(7,eq_ref(a(A),cost([],[],[],[],1),[1:dec_pos(A,B)],[a(B)],[1:dec_pos(A,B),a(B)],Cs7,[(refined,refined(2)),(termination,terminating)])),
		(8,eq_ref(a(A),cost([],[],[],[],1),[2:dec_pos(A,B)],[a(B)],[2:dec_pos(A,B),a(B)],Cs8,[(refined,refined(2)),(termination,terminating)])),
		%not all the combinations are possible
	(9,eq_ref(a(A),cost([],[],[],[],1),[1:dec_pos(A,B),1:dec_pos(B,C)],[a(C)],[1:dec_pos(A,B),1:dec_pos(B,C),a(C)],Cs9,[(refined,refined(3)),(termination,terminating)])),
	(10,eq_ref(a(A),cost([],[],[],[],1),[1:dec_pos(A,B),2:dec_pos(B,C)],[a(C)],[1:dec_pos(A,B),2:dec_pos(B,C),a(C)],Cs10,[(refined,refined(3)),(termination,terminating)]))
		],
	assertion(nad_equals(Cs7,[A>=1,B=A-1])),
	assertion(nad_equals(Cs8,[A=0,B=A])),
	assertion(nad_equals(Cs9,[A>=1,B=A-1,B>=1,C=B-1])),
	assertion(nad_equals(Cs10,[A>=1,B=A-1,C=B,B=0])).



test(unfold_non_terminating):-
	create_crse(crse_unfold2,CRSE),	
	CRSE=crse(_,CRS),
	crs_get_cr(CRS,a,CRa),
	crs_get_cr(CRS,dec_pos,CRdec),
	External_patts=external_patterns(dec_pos(Ap,Bp),[
		(1,external_pattern([termination(non_terminating),summary([Ap>=1,Bp=Ap-1])])),
		(2,external_pattern([termination(terminating),summary([Ap=<0,Bp=Ap])]))
		]),
	cr_set_external_patterns(CRdec,External_patts,CRdec2),
	crs_update_cr(CRS,dec_pos,CRdec2,CRS2),
	cr_specialize(CRa,CRS2,CRa2),
	cr_get_ceList_with_id(CRa2,ListEqs),
	ListEqs=
		[
		(6,eq_ref(a(A),cost([],[],[],[],1),[],[],[],[],[(refined,refined(1)),(termination,terminating)])),

		(7,eq_ref(a(A),cost([],[],[],[],1),[1:dec_pos(A,B)],[],[1:dec_pos(A,B)],Cs7,[(refined,refined(2)),(termination,non_terminating)])),
		(8,eq_ref(a(A),cost([],[],[],[],1),[2:dec_pos(A,B)],[a(B)],[2:dec_pos(A,B),a(B)],Cs8,[(refined,refined(2)),(termination,terminating)])),
		%in this case there is only one specialization of 3
		(9,eq_ref(a(A),cost([],[],[],[],1),[1:dec_pos(A,B)],[],[1:dec_pos(A,B)],Cs9,[(refined,refined(3)),(termination,non_terminating)]))
		],
	assertion(nad_equals(Cs7,[A>=1,B=A-1])),
	assertion(nad_equals(Cs8,[A=0,B=A])),
	assertion(nad_equals(Cs9,[A>=1,B=A-1])).
	
test(external_patterns_basic):-
	create_crse(crse_unfold2,CRSE),	
	CRSE=crse(_,CRS),
	crs_get_cr(CRS,dec_pos,CRdec),
	compute_loops(CRdec,0,Loops),
	compute_chains(Loops,Chains,_),
	compute_backward_invariants(Loops,Chains,Backward_invs),
	chains_annotate_termination(Chains,Loops,Chains2),
	cr_compute_external_execution_patterns(Chains2,Backward_invs,0,External_patterns),
	External_patterns=external_patterns(dec_pos(Ap,Bp),[
		([[1]],external_pattern([termination(terminating),summary(Cs1)])),
		([[2]],external_pattern([termination(terminating),summary(Cs2)]))
		]),
	assertion(nad_equals(Cs1,[Ap>=1,Bp=Ap-1])),
	assertion(nad_equals(Cs2,[Ap=<0,Bp=Ap])).
	
	

crs_test:crse_example(crse_external_patterns_compress,[
	eq_ref(a(A,B),cost([],[],[],[],1),[],[],[],[A+1>=B],[]),
	eq_ref(a(A,B),cost([],[],[],[],2),[],[],[],[ A>=B ],[]),
	eq_ref(a(A,B),cost([],[],[],[],1),[],[a(A2,B2)],[a(A2,B2)],[ A+1=<B,A2=A+1 ],[])
	],[entry(a(A,B),[])]).	
	
test(external_patterns_compress):-
	create_crse(crse_external_patterns_compress,CRSE),	
	CRSE=crse(_,CRS),
	crs_get_cr(CRS,a,CRa),
	compute_loops(CRa,0,Loops),
	compute_chains(Loops,Chains,_),
	compute_backward_invariants(Loops,Chains,Backward_invs),
	chains_annotate_termination(Chains,Loops,Chains2),
	cr_compute_external_execution_patterns(Chains2,Backward_invs,0,External_patterns0),
	External_patterns0=external_patterns(a(Ap,Bp),[
		([[1]],external_pattern([termination(terminating),summary(Cs1)])),
		([[2]],external_pattern([termination(terminating),summary(Cs2)])),
		([[[3]]],external_pattern([termination(non_terminating),summary(Cs3)])),
		([[[3],1]],external_pattern([termination(terminating),summary(Cs4)])),
		([[[3],2]],external_pattern([termination(terminating),summary(Cs5)]))
		]),
	assertion(nad_equals(Cs1,[Ap>=Bp])),
	assertion(nad_equals(Cs2,[Ap+1>=Bp])),
	assertion(nad_equals(Cs3,[Ap+1=< Bp])),
	assertion(nad_equals(Cs4,[Ap+1=< Bp])),
	assertion(nad_equals(Cs5,[Ap+1=< Bp])),

	cr_compute_external_execution_patterns(Chains2,Backward_invs,1,External_patterns1),
	External_patterns1=external_patterns(a(Ap,Bp),[
		([[1]],external_pattern([termination(terminating),summary(Cs11)])),
		([[2]],external_pattern([termination(terminating),summary(Cs12)])),
		([[[3]]],external_pattern([termination(non_terminating),summary(Cs14)])),
		([ [[3],1], [[3],2]],external_pattern([termination(terminating),summary(Cs13)]))
		]),
	assertion(nad_equals(Cs11,[Ap>=Bp])),
	assertion(nad_equals(Cs12,[Ap+1>=Bp])),
	assertion(nad_equals(Cs13,[Ap+1=< Bp])),
	assertion(nad_equals(Cs14,[Ap+1=< Bp])),

	cr_compute_external_execution_patterns(Chains2,Backward_invs,2,External_patterns2),
	External_patterns2=external_patterns(a(Ap,Bp),[
		([[1],[2]],external_pattern([termination(terminating),summary(Cs21)])),
		([[[3]]],external_pattern([termination(non_terminating),summary(Cs23)])),
		([ [[3],1], [[3],2]],external_pattern([termination(terminating),summary(Cs22)]))
		]),
	assertion(nad_equals(Cs21,[Ap+1>=Bp])),
	assertion(nad_equals(Cs22,[Ap+1=< Bp])),
	assertion(nad_equals(Cs23,[Ap+1=< Bp])).


	
%test(external_patterns_non_terminating):-
	
:-end_tests(unfolding).