:- module(cost_equation_solver_test,[
		
	]).


	
:-begin_tests(cost_equation_solver).


:-use_module(cost_equation_solver).
:-use_module('../refinement/loops',[
	compute_loops/3,
	loops_get_loop/3,
	loop_get_cost/2]).
:-use_module('../utils/cost_structures',[
	init_cost_structures/0,
	cstr_from_cexpr/2]).
:-use_module('../utils/crs.plt',[create_crse/2]).
:-use_module('../utils/crs',[
	crs_get_cr/3,
	cr_set_external_patterns/3,
	crs_update_cr/4,
	cr_get_ce_by_id/3,
	ce_get_cost/2
	]).

crs_test:crse_example(crse_amortized,[
	eq_ref(a(A),cost([],[],[],[],1),[1:l1(A2,B),1:l2(B2,C)],[],[1:l1(A2,B),1:l2(B2,C)],[A2>=B,B2>=C,A2=A,B2=B,C>=0],[]),
	eq_ref(a(A),cost([],[],[],[],1),[1:l1(A2,B),1:l2(B2,C)],[a(C2)],[1:l1(A2,B),1:l2(B2,C),a(C2)],[A2>=B,B2>=C,A2=A,B2=B,C=C2,C>=0 ],[]),

	
	%these are stubs so the corresponding crs exist
	eq_ref(l1(A,B),cost([],[],[],[],1),[],[],[],[],[]),
	eq_ref(l2(A,B),cost([],[],[],[],1),[],[],[],[],[])

	],[entry(a(A),[])]).


test(ce_cost_sequential_amortized):-
	init_cost_structures,
	create_crse(crse_amortized,CRSE),	
	CRSE=crse(_,CRS),
	cstr_from_cexpr(nat(Ap-Bp),Cost_l1),
	cstr_from_cexpr(nat(Ap-Bp),Cost_l2),
	%put the external patterns with cost
	crs_get_cr(CRS,l1,CR_l1),
	External_patts_l1=external_patterns(l1(Ap,Bp),[
		(1,external_pattern([cost(Cost_l1)]))
		]),
	cr_set_external_patterns(CR_l1,External_patts_l1,CR_l1p),
	crs_update_cr(CRS,l1,CR_l1p,CRS2),
	
	crs_get_cr(CRS,l2,CR_l2),
		
	External_patts_l2=external_patterns(l2(Ap,Bp),[
		(1,external_pattern([cost(Cost_l2)]))
		]),
	cr_set_external_patterns(CR_l2,External_patts_l2,CR_l2p),
	crs_update_cr(CRS2,l2,CR_l2p,CRS3),
	
	crs_get_cr(CRS3,a,CRa),
	compute_ce_bounds(CRa,CRS3,CRa2),
	
	cr_get_ce_by_id(CRa2,1,CE1),
	ce_get_cost(CE1,Cost_ce1),
	assertion(Cost_ce1=cost([bound(ub,[(A,1)]+0,[Iv1,Iv2])],[],[],[(Iv1,1),(Iv2,1)],1)),
	
	cr_get_ce_by_id(CRa2,2,CE2),
	ce_get_cost(CE2,Cost_ce2),
	assertion(Cost_ce2=cost([bound(ub,[(A,1),(B,-1)]+0,[Iv1,Iv2])],[bound(lb,[(A,1),(B,-1)]+0,[Iv1,Iv2])],[],[(Iv1,1),(Iv2,1)],1)),
	
	
	%test loops
	compute_loops(CRa2,0,Loops),
	compute_loop_bounds(Loops,CRa2,Loops2),
	loops_get_loop(Loops2,1,Loop1),
	assertion(loop_get_cost(Loop1,Cost_ce1)),
	loops_get_loop(Loops2,2,Loop2),
	assertion(loop_get_cost(Loop2,Cost_ce2)).
	



	
	
:-end_tests(cost_equation_solver).