

:-begin_tests(invariants).

:-use_module(invariants).
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
	trace,
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
	trace,
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
%compute_forward_invariants/4,
		      
%fwd_invs_get_infeasible_prefixes/2,
%back_invs_get_infeasible/2,
		      
%fwd_invs_get_loop_invariants/2
%back_invs_get_loop_invariants/2,
%loop_invs_to_CE_invs/3

:-end_tests(invariants).
