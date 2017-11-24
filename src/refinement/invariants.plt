

:-begin_tests(invariants).

:-use_module(invariants).
:-use_module(chains,[chains_update_with_discarded_loops/4]).
:-use_module(stdlib(numeric_abstract_domains),[nad_equals/2,nad_consistent_constraints/1]).

test(backward_invariants):-
	Chains=chains(_,[
				[3,[2],1],
				[[4],3,[2],1]
				]),
	Loops=loops(range(1,5),[
	(1,loop(a(A,B),[],[A=0,B=0],[eqs([1]),terminating])),
	(2,loop(a(A,B),[a(A2,B2)],[A=<9,A2=A-1,B2=B-2],[eqs([2,3]),terminating])),
	(3,loop(a(A,B),[a(A2,B2)],[A=10,A2=A-1,B2=B-2],[eqs([4]),terminating])),
	(4,loop(a(A,B),[a(A2,B2)],[A>=11,A2=A-1,B2=B-2],[eqs([4]),terminating]))
	]),
	compute_backward_invariants(Loops,Chains,Back_invs),
	back_invs_get(Back_invs,[1],inv(a(C,D),Inv1_star,Inv1_plus)),
	assertion(Inv1_star=[]),
	assertion(nad_equals(Inv1_plus,[C=0,D=0])),
	
	back_invs_get(Back_invs,[[2],1],inv(a(C,D),Inv21_star,Inv21_plus)),
	assertion(nad_equals(Inv21_star,[D=2*C,C>=0])),
	assertion(nad_equals(Inv21_plus,[D=2*C,C>=1,C=<9])),
	
	back_invs_get(Back_invs,[3,[2],1],inv(a(C,D),Inv321_star,Inv321_plus)),
	assertion(nad_equals(Inv321_star,[D=2*C,C>=1,C=<9])),
	assertion(nad_equals(Inv321_plus,[D=2*C,C=10])),
	
	back_invs_get(Back_invs,[[4],3,[2],1],inv(a(C,D),Inv4321_star,Inv4321_plus)),
	assertion(nad_equals(Inv4321_star,[D=2*C,C>=10])),
	assertion(nad_equals(Inv4321_plus,[D=2*C,C>=11])),
	back_invs_get_infeasible(Back_invs,[]).



test(backward_invariants_unfeasible_and_divergent):-
	Chains=chains(_,[
				[[4],3,[2],1],
				[[4],3,[2]]
				]),
	Loops=loops(range(1,5),[
	(1,loop(a(A,B,C),[],[A=0,B=0,C=0],[eqs([1]),terminating])),
	(2,loop(a(A,B,C),[a(A2,B2,C2)],[C2=C,A=<9,A2=A-1,B2=B-2],[eqs([2,3]),terminating])),
	(3,loop(a(A,B,C),[a(A2,B2,C2)],[C2=C,A=10,A2=A-1,B2=B-2,C=1],[eqs([4]),terminating])),
	(4,loop(a(A,B,C),[a(A2,B2,C2)],[C2=C,A>=11,A2=A-1,B2=B-2],[eqs([4]),terminating]))
	]),
	%Unfeasible
	compute_backward_invariants(Loops,Chains,Back_invs),
	back_invs_get(Back_invs,[1],inv(a(C,D,E),Inv1_star,Inv1_plus)),
	assertion(Inv1_star=[]),
	assertion(nad_equals(Inv1_plus,[C=0,D=0,E=0])),
	
	back_invs_get(Back_invs,[[2],1],inv(a(C,D,E),Inv21_star,Inv21_plus)),
	assertion(nad_equals(Inv21_star,[D=2*C,C>=0,E=0])),
	assertion(nad_equals(Inv21_plus,[D=2*C,C>=1,C=<9,E=0])),
	
	back_invs_get(Back_invs,[3,[2],1],inv(a(C,D,E),Inv321_star,Inv321_plus)),
	assertion(nad_equals(Inv321_star,[D=2*C,C>=1,C=<9,E=0])),
	assertion(nad_equals(Inv321_plus,[1=0])),
	
	back_invs_get(Back_invs,[[4],3,[2],1],inv(a(C,D,E),Inv4321_star,Inv4321_plus)),
	assertion(nad_equals(Inv4321_star,[1=0])),
	assertion(nad_equals(Inv4321_plus,[1=0])),
	assertion(back_invs_get_infeasible(Back_invs,[
		[3,[2],1],
		[[4],3,[2],1]
	])),
	
	%Divergent
	back_invs_get(Back_invs,[[2]],inv(a(C,D,E),Inv2_star,Inv2_plus)),
	assertion(nad_equals(Inv2_star,[])),
	assertion(nad_equals(Inv2_plus,[C=<9])),
	
	back_invs_get(Back_invs,[3,[2]],inv(a(C,D,E),Inv32_star,Inv32_plus)),
	assertion(nad_equals(Inv32_star,[C=<9])),
	assertion(nad_equals(Inv32_plus,[C=10,E=1])),
	
	back_invs_get(Back_invs,[[4],3,[2]],inv(a(C,D,E),Inv432_star,Inv432_plus)),
	assertion(nad_equals(Inv432_star,[C>=10,E=1])),
	assertion(nad_equals(Inv432_plus,[C>=11,E=1])).
	

		
test(multiple):-
	Chains=chains(_,[
				[[4],multiple(3,[ [[2],1],[1]])]
				]),
	Loops=loops(range(1,5),[
	(1,loop(a(A,B,C),[],[C>=1,A=0,B=0],[eqs([1]),terminating])),
	(2,loop(a(A,B,C),[a(A2,B2,C2)],[C>=1,C2=C,A=<9,A2=A-1,B2=B-2],[eqs([2,3]),terminating])),
	(3,loop(a(A,B,C),[a(A2,B2,C2),a(A3,B3,C3)],[C>=1,C2=C,C3=C,
												A=10,A2=A-C,B2=B-2*C,
												A3=A-1,B3=B-2],[eqs([4]),terminating])),
	(4,loop(a(A,B,C),[a(A2,B2,C2)],[C>=1,C2=C,A>=11,A2=A-1,B2=B-2],[eqs([4]),terminating]))
	]),
	compute_backward_invariants(Loops,Chains,Back_invs),
	back_invs_get(Back_invs,[1],inv(a(C,D,E),Inv1_star,Inv1_plus)),
	assertion(Inv1_star=[]),
	assertion(nad_equals(Inv1_plus,[C=0,D=0,E>=1])),

								
	back_invs_get(Back_invs,[[2],1],inv(a(C,D,E),Inv21_star,Inv21_plus)),
	assertion(nad_equals(Inv21_star,[D=2*C,C>=0,E>=1])),
	assertion(nad_equals(Inv21_plus,[D=2*C,C>=1,C=<9,E>=1])),
	
	back_invs_get(Back_invs,[multiple(3,[ [[2],1],[1]])],inv(a(C,D,E),Inv321_star,Inv321_plus)),
	assertion(nad_equals(Inv321_star,[D=2*C,C>=0,C=<9,E>=1])),
	assertion(nad_equals(Inv321_plus,[D=2*C,C=10,E>=1,E=<10])).


test(multiple2):-
	Chains=chains(_,[
				[[4],multiple([3],[ [[2],1],[1]])]
				]),
	Loops=loops(range(1,5),[
	(1,loop(a(A,B,C),[],[C>=1,A=0,B=0],[eqs([1]),terminating])),
	(2,loop(a(A,B,C),[a(A2,B2,C2)],[C>=1,C2=C,A=<9,A2=A-1,B2=B-2],[eqs([2,3]),terminating])),
	(3,loop(a(A,B,C),[a(A2,B2,C2),a(A3,B3,C3)],[C>=1,C2=C,C3=C,
												A>=10,A2=A-C,B2=B-2*C,
												A3=A-1,B3=B-2],[eqs([4]),terminating])),
	(4,loop(a(A,B,C),[a(A2,B2,C2)],[C>=1,C2=C,A>=11,A2=A-1,B2=B-2],[eqs([4]),terminating]))
	]),
	compute_backward_invariants(Loops,Chains,Back_invs),

	back_invs_get(Back_invs,[multiple([3],[ [[2],1],[1]])],inv(a(C,D,E),Inv321_star,Inv321_plus)),
	assertion(nad_equals(Inv321_star,[D=2*C,C>=0,E>=1])),
	assertion(nad_equals(Inv321_plus,[D=2*C,C>=10,E>=1,E=< C])).
	
test(unfeasible_in_multiple):-
	Chains=chains(_,[
				[[4],multiple([3],[ [[2],1],[1],[4,5,6]])]
				]),
	Loops=loops(range(1,5),[
	(1,loop(a(A,B,C),[],[C>=1,A=0,B=0],[eqs([1]),terminating])),
	(2,loop(a(A,B,C),[a(A2,B2,C2)],[C>=1,C2=C,A=<9,A2=A-1,B2=B-2],[eqs([2,3]),terminating])),
	(3,loop(a(A,B,C),[a(A2,B2,C2),a(A3,B3,C3)],[C>=1,C2=C,C3=C,
												A>=10,A2=A-C,B2=B-2*C,
												A3=A-1,B3=B-2],[eqs([4]),terminating])),
	(4,loop(a(A,B,C),[a(A2,B2,C2)],[A=2,A2=A-1,B2=B,C2=C,C=2],[eqs([5]),terminating])),
	(5,loop(a(A,B,C),[a(A2,B2,C2)],[A=1,A2=A-1,B2=B,C2=C],[eqs([6]),terminating])),
	(6,loop(a(A,B,C),[],[A=0,C=0],[eqs([7]),terminating]))
	]),
	compute_backward_invariants(Loops,Chains,Back_invs),
	
	%the chain [4,5,6] is infeasible
	back_invs_get(Back_invs,[4,5,6],inv(a(C,D,E),_Inv456_star,Inv456_plus)),
	assertion(nad_equals(Inv456_plus,[1=0])),
	
	% the additional tail does not change anything because it is infeasible
	back_invs_get(Back_invs,[multiple([3],[ [[2],1],[1],[4,5,6]])],inv(a(C,D,E),Inv321_star,Inv321_plus)),
	assertion(nad_equals(Inv321_star,[D=2*C,C>=0,E>=1])),
	assertion(nad_equals(Inv321_plus,[D=2*C,C>=10,E>=1,E=< C])),
	back_invs_get_infeasible(Back_invs,Infeasible),
	assertion(Infeasible=[
	[4,5,6],
	[[4],multiple([3],[ [[2],1],[1],[4,5,6]])]
	]).	

test(forward_invariants):-
	Chains=chains(_,[
				[1],
				[[2],1],
				[3,[2],1],
				[[4],3,[2],1]
				]),
	Loops=loops(range(1,5),[
	(1,loop(a(A,B),[],[A=0,B=0],[eqs([1]),terminating])),
	(2,loop(a(A,B),[a(A2,B2)],[A=<9,A2=A-1,B2=B-2],[eqs([2,3]),terminating])),
	(3,loop(a(A,B),[a(A2,B2)],[A=10,A2=A-1,B2=B-2],[eqs([4]),terminating])),
	(4,loop(a(A,B),[a(A2,B2)],[A>=11,A2=A-1,B2=B-2],[eqs([4]),terminating]))
	]),
	compute_forward_invariants(fwd_inv(a(A,_),[A=20]),Loops,Chains,Fwd_invs),
	fwd_invs_get(Fwd_invs,[[2]],inv(a(Ap,_),Inv2_star,Inv2_plus)),
	assertion(nad_equals(Inv2_star,[Ap=20])),
	assertion(nad_equals(Inv2_plus,[1=0])),
	fwd_invs_get(Fwd_invs,[3],inv(a(Ap,_),Inv3_star,Inv3_plus)),
	assertion(nad_equals(Inv3_star,[Ap=20])),
	assertion(nad_equals(Inv3_plus,[1=0])),
	fwd_invs_get(Fwd_invs,[[4]],inv(a(Ap,_),Inv4_star,Inv4_plus)),
	assertion(nad_equals(Inv4_star,[Ap=<20])),
	assertion(nad_equals(Inv4_plus,[Ap=<19,Ap >=10])),
	fwd_invs_get(Fwd_invs,[3,[4]],inv(a(Ap,_),Inv34_star,Inv34_plus)),
	assertion(nad_equals(Inv34_star,[Ap=<19,Ap>=10])),
	assertion(nad_equals(Inv34_plus,[Ap =9])),
	
	assertion(\+fwd_invs_get(Fwd_invs,[[2],3],_)),
	fwd_invs_get_infeasible_prefixes(Fwd_invs,Infeasible),
	assertion(Infeasible=[
	    [1],
		[3],
		[[2]]
		]).

test(forward_multiple):-
	Chains=chains(_,[
				[[7],multiple([3],[ [[2],1],[1],[4,5,6]])]
				]),
	Loops=loops(range(1,5),[
	(1,loop(a(A,B,C),[],[C>=1,A=0,B=0],[eqs([1]),terminating])),
	(2,loop(a(A,B,C),[a(A2,B2,C2)],[C>=1,C2=C,A=<9,A2=A-1,B2=B-2],[eqs([2,3]),terminating])),
	(3,loop(a(A,B,C),[a(A2,B2,C2),a(A3,B3,C3)],[C>=1,C2=C,C3=C,
												A>=10,A2=A-C,B2=B-2*C,
												A3=A-1,B3=B-2],[eqs([4]),terminating])),
	(4,loop(a(A,B,C),[a(A2,B2,C2)],[A=2,A2=A-1,B2=B,C2=C,C=2],[eqs([5]),terminating])),
	(5,loop(a(A,B,C),[a(A2,B2,C2)],[A=1,A2=A-1,B2=B,C2=C,C=1],[eqs([6]),terminating])),
	(6,loop(a(A,B,C),[],[A=0,C=0],[eqs([7]),terminating])),
	(7,loop(a(A,B,C),[a(A2,B2,C2)],[A>=1,A2=A-1],[eqs([8]),terminating]))
	]),

	compute_forward_invariants(fwd_inv(a(A,_,_),[]),Loops,Chains,Fwd_invs),
	fwd_invs_get(Fwd_invs,[[7]],inv(a(Ap,_,_),_,Inv7_plus)),
	assertion(nad_equals(Inv7_plus,[Ap>=0])),
	
	fwd_invs_get(Fwd_invs,[[3],[7]],inv(a(Ap,_,Cp),_,Inv37_plus)),
	assertion(nad_equals(Inv37_plus,[Ap+Cp>=10,Cp>=1])),
	
	fwd_invs_get(Fwd_invs,[[2],[3],[7]],inv(a(Ap,_,Cp),_,Inv237_plus)),
	assertion(nad_equals(Inv237_plus,[Ap=<8,Cp>=1])),
	
	fwd_invs_get(Fwd_invs,[4,[3],[7]],inv(a(Ap,_,Cp),_,Inv437_plus)),
	assertion(nad_equals(Inv437_plus,[1=0])),

	%because
	%\+nad_consistent_constraints([A=2,A2=A-1,B2=B,C2=C,C=2,  A+C>=10,C>=1]),
	assertion(\+fwd_invs_get(Fwd_invs,[5,4,[3],[7]],_)),
	fwd_invs_get_infeasible_prefixes(Fwd_invs,Infeasible),
	assertion(Infeasible=[
		[4,[3],[7]]
		]).


test(fwd_loop_invariants_and_CE_invariants):-
	Loops=loops(range(2,5),[
	(2,loop(a(A,B,C),[a(A2,B2,C2)],[],[eqs([2,3]),terminating])),
	(3,loop(a(A,B,C),[a(A2,B2,C2),a(_,_,_)],[],[eqs([4]),terminating])),
	(4,loop(a(A,B,C),[a(A2,B2,C2)],[],[eqs([5]),terminating]))
	]),
	
	invariants:fwd_invs_empty(fwd_inv(a(A,B,C),[A>=1]),Fwd_invs),
	invariants:fwd_invs_add(Fwd_invs,[[2]],inv(a(Ap,Bp,Cp),[Ap>=1],[Ap>=2,Bp=1]),Fwd_invs2),
	invariants:fwd_invs_add(Fwd_invs2,[[3]],inv(a(Ap,Bp,Cp),[Ap>=0],[Ap>=3,Bp=2]),Fwd_invs3),
	invariants:fwd_invs_add(Fwd_invs3,[[4],[2]],inv(a(Ap,Bp,Cp),[Ap>=2,Bp=1],[]),Fwd_invs4),
	invariants:fwd_invs_add(Fwd_invs4,[[4],[3]],inv(a(Ap,Bp,Cp),[Ap>=3,Bp=2],[]),Fwd_invs5),
	
	fwd_invs_get_loop_invariants(Fwd_invs5,Loop_invs),
	loop_invs_get(Loop_invs,4,inv(a(A,B,C),Inv4)),
	assertion(nad_equals(Inv4,[A >=1+B,B>=1,B=<2])),
	
	loop_invs_get(Loop_invs,2,inv(a(A,B,C),Inv2)),
	assertion(nad_equals(Inv2,[A>=1])),
	
	loop_invs_to_CE_invs(Loop_invs,Loops,CE_invs),
	
	ce_invs_get(CE_invs,5,inv(a(A,B,C),InvCE5)),
	assertion(nad_equals(InvCE5,[A >=1+B,B>=1,B=<2])),
	
	ce_invs_get(CE_invs,2,inv(a(A,B,C),InvCE2)),
	ce_invs_get(CE_invs,2,inv(a(A,B,C),InvCE3)),
	assertion(nad_equals(InvCE2,InvCE3)).
	
	
test(back_loop_invariants):-
	invariants:back_invs_empty(a(A,B,C),Back_invs),
	invariants:back_invs_add(Back_invs,[[2]],inv(a(Ap,Bp,Cp),[Ap>=1],[Ap>=2,Bp=1]),Back_invs2),
	invariants:back_invs_add(Back_invs2,[[3]],inv(a(Ap,Bp,Cp),[Ap>=1],[Ap>=3,Bp=2]),Back_invs3),
	invariants:back_invs_add(Back_invs3,[[4],[2]],inv(a(Ap,Bp,Cp),[Ap>=2,Bp=1],[]),Back_invs4),
	invariants:back_invs_add(Back_invs4,[[4],[3]],inv(a(Ap,Bp,Cp),[Ap>=3,Bp=2],[]),Back_invs5),
	
	back_invs_get_loop_invariants(Back_invs5,Loop_invs),
	loop_invs_get(Loop_invs,4,inv(a(A,B,C),Inv4)),
	assertion(nad_equals(Inv4,[A >=1+B,B>=1,B=<2])),
	
	loop_invs_get(Loop_invs,2,inv(a(A,B,C),Inv2)),
	assertion(nad_equals(Inv2,[A>=1])).	

test(back_invs_update_with_changed_chains):-
	Chains=chains([[4],[3],[2,5],1],[
				[[4],multiple([3],[ [[2,5],1],[1]])]
				]),
	Loops=loops(range(1,6),[
	(1,loop(a(A,B,C),[],[C>=1,A=0,B=0],[eqs([1]),terminating])),
	(2,loop(a(A,B,C),[a(A2,B2,C2)],[C>=1,C2=C,A=<9,A2=A-1,B2=B-2],[eqs([2,3]),terminating])),
	(3,loop(a(A,B,C),[a(A2,B2,C2),a(A3,B3,C3)],[C>=1,C2=C,C3=C,
												A>=10,A2=A-C,B2=B-2*C,
												A3=A-1,B3=B-2],[eqs([4]),terminating])),
	(4,loop(a(A,B,C),[a(A2,B2,C2)],[C>=1,C2=C,A>=11,A2=A-1,B2=B-2],[eqs([4]),terminating])),
	%for this example 5 is equal to 2 so the invariants are the same
	(5,loop(a(A,B,C),[a(A2,B2,C2)],[C>=1,C2=C,A=<9,A2=A-1,B2=B-2],[eqs([6]),terminating]))
	
	]),
	compute_backward_invariants(Loops,Chains,Back_invs),
	chains_update_with_discarded_loops(Chains,[5],_,Changes_map),
	back_invs_update_with_changed_chains(Back_invs,Changes_map,Back_invs2),
	
	
	back_invs_get(Back_invs,[multiple([3],[ [[2,5],1],[1]])],inv(a(C,D,E),Inv1_star,Inv1_plus)),
	back_invs_get(Back_invs2,[multiple([3],[ [[2],1],[1]])],inv(a(C,D,E),Inv2_star,Inv2_plus)),
	assertion(Inv1_star==Inv2_star),
	assertion(Inv1_plus==Inv2_plus),
	assertion(\+back_invs_get(Back_invs2,[multiple(3,[ [[2,5],1],[1]])],_)).
	
	
test(fwd_invs_update_with_discarded_loops):-
	Chains=chains([[4],[3],[2,5],1],[
				[[4],multiple([3],[ [[2,5],1],[1]])]
				]),
	Loops=loops(range(1,6),[
	(1,loop(a(A,B,C),[],[C>=1,A=0,B=0],[eqs([1]),terminating])),
	(2,loop(a(A,B,C),[a(A2,B2,C2)],[C>=1,C2=C,A=<9,A2=A-1,B2=B-2],[eqs([2,3]),terminating])),
	(3,loop(a(A,B,C),[a(A2,B2,C2),a(A3,B3,C3)],[C>=1,C2=C,C3=C,
												A>=10,A2=A-C,B2=B-2*C,
												A3=A-1,B3=B-2],[eqs([4]),terminating])),
	(4,loop(a(A,B,C),[a(A2,B2,C2)],[C>=1,C2=C,A>=11,A2=A-1,B2=B-2],[eqs([4]),terminating])),
	%for this example 5 is equal to 2 so the invariants are the same
	(5,loop(a(A,B,C),[a(A2,B2,C2)],[C>=1,C2=C,A=<9,A2=A-1,B2=B-2],[eqs([6]),terminating]))
	
	]),
	compute_forward_invariants(fwd_inv(a(_,_,_),[]),Loops,Chains,Fwd_invs),
	fwd_invs_update_with_discarded_loops(Fwd_invs,[5],Fwd_invs2),
	
	fwd_invs_get(Fwd_invs,[[2,5],[3],[4]],inv(a(C,D,E),Inv1_star,Inv1_plus)),
	fwd_invs_get(Fwd_invs2,[[2],[3],[4]],inv(a(C,D,E),Inv2_star,Inv2_plus)),
	assertion(Inv1_star==Inv2_star),
	assertion(Inv1_plus==Inv2_plus),
	assertion(\+fwd_invs_get(Fwd_invs2,[[2,5],[3],[4]],_)).
%fwd_invs_get_loop_invariants/2
%back_invs_get_loop_invariants/2,
%loop_invs_to_CE_invs/3

:-end_tests(invariants).
