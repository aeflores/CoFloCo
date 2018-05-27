
	
:-begin_tests(chains).

:-use_module(chains).
:-use_module(invariants).

loops_example(sequence,
	loops(range(1,6),[
	(1,loop(a(A),[],[],[])),
	(2,loop(a(A),[],[A=20],[])),
	(3,loop(a(A),[a(A2)],[1*A=10,A2=A+1],[])),
	(4,loop(a(A),[a(A2)],[1*A>=11,A2=A+1],[])),
	(5,loop(a(A),[a(A2)],[1*A=<9,A2=A+1],[]))
	])).

loops_example(sequence_incompatible,
	loops(range(1,6),[
	(1,loop(a(A,B),[],[],[])),
	(2,loop(a(A,B),[],[A=20],[])),
	(3,loop(a(A,B),[a(A2,B2)],[B2=B,1*A=10,A2=A+1],[])),
	(4,loop(a(A,B),[a(A2,B2)],[B2=B,1*A>=11,A2=A+1,B=1],[])),
	(5,loop(a(A,B),[a(A2,B2)],[B2=B,1*A=<9,A2=A+1,B=0],[]))
	])).	
		
loops_example(alternative,
	loops(range(1,4),[
	(1,loop(a(A),[],[A=0],[])),
	(2,loop(a(A),[a(A2)],[1*A>=1,A2=A-1],[])),
	(3,loop(a(A),[a(A2)],[1*A+1=<0,A2=A+1],[]))
	])).

loops_example(all_possible,
	loops(range(1,4),[
	(1,loop(a(A,B,C),[],[A=0],[])),
	(2,loop(a(A,B,C),[a(A,B,C)],[A=1],[])),
	(3,loop(a(A,B,C),[a(A,B,C)],[B=1],[])),
	(4,loop(a(A,B,C),[a(A,B,C)],[C=1],[]))
	])).
	
loops_example(multiple,
	loops(range(1,4),[
	(1,loop(a(A),[],[A=0],[])),
	(2,loop(a(A),[a(A2),a(A2)],[A=1,A2=A-1],[])),
	(3,loop(a(A),[a(A2),a(A2)],[A>=1,A2=A-1],[])),
	(4,loop(a(A),[a(A)],[A>=10,A2=A-1],[]))
	])).
		
test(chains_sequence):-
	loops_example(sequence,Loops),
	compute_chains(Loops,chains(Phases,Chains),_),
	assertion(Phases=[phase([5],[]),phase(3,[]),phase([4],[]),phase(2,[]),phase(1,[])]),
	assertion(Chains=[
	[1],
	[2],
	
	[3,1],
	[3,[4]],
	[3,[4],1],
	[3,[4],2],
	
		
	[[4]],
	[[4],1],
	[[4],2],
	
	
	[[5]],
	[[5],1],
	[[5],3,1],
	[[5],3,[4]],
	[[5],3,[4],1],
	[[5],3,[4],2]	
	]).

	
test(chains_alternative):-
	loops_example(alternative,Loops),
	compute_chains(Loops,chains(Phases,Chains),_),
	assertion(Phases=[phase([3],[]),phase([2],[]),phase(1,[])]),
	assertion(Chains=[
	[1],
	[[2]],
    [[2],1],
  
    [[3]],
    [[3],1]
	]).	
	
	
	
test(chains_all_possible):-
	loops_example(all_possible,Loops),
	compute_chains(Loops,chains(Phases,Chains),_),
	assertion(Phases=[phase([2,3,4],[]),phase(1,[])]),
	assertion(Chains=[
	[1],
	[[2,3,4]],
    [[2,3,4],1]
	]).	
test(chains_multiple):-
	loops_example(multiple,Loops),
	compute_chains(Loops,chains(Phases,Chains),_),
	assertion(Phases=[phase([3,4],[]),phase(2,[]),phase(1,[])]),
	assertion(Chains=[
	[1],
	[multiple(2,[[1]])],
	[multiple([3,4],[[],[1],[multiple(2,[[1]])]])]
	]).		


test(chains_discard_infeasible):-
	Chains=chains(_,[
	[1],
	[2],	
	[[4]],
	[[4],1],
	[[4],2],
	[multiple([3],[
			[1],
			[2],
			[[4]],
			[[4],1],
			[[4],2]
			])]
	]),
	Infeasible=[[1],[[4],1]],
	chains_discard_infeasible(Chains,Infeasible,chains(_,ChainsRest),Changes),
	assertion(ChainsRest=
	[
	[2],	
	[[4]],
	[[4],2],
	[multiple([3],[
			[2],
			[[4]],
			[[4],2]
			])]
	]),
	assertion(Changes=[
	([1],none),
	([[4],1],none),
	(
				[multiple([3],[
				[1],
				[2],
				[[4]],
				[[4],1],
				[[4],2]
				])]
			,
				[multiple([3],[
				[2],
				[[4]],
				[[4],2]
				])]
			)
			]),
	Infeasible2=[[1],[[4],1],[multiple([3],[
			[1],
			[2],
			[[4]],
			[[4],1],
			[[4],2]
			])]],
		chains_discard_infeasible(Chains,Infeasible2,chains(_,ChainsRest2),Changes2),
	assertion(ChainsRest2=[
		[2],	
		[[4]],
		[[4],2]
	]),
	Changes2=[
		([1],none),
		([[4],1],none),
		([multiple([3],[
			[1],
			[2],
			[[4]],
			[[4],1],
			[[4],2]
			])],none)
	].




test(chains_discard_infeasible_prefixes):-
	Chains=chains(_,[
	[1],
	[2],	
	[[4]],
	[[4],1],
	[[4],2],
	[multiple([3],[
			[1],
			[2],
			[[4]],
			[[4],1],
			[[4],2]
			])]
	]),
	Infeasible=[
	[[4]],
	[[4],[3]]
	],
	sort(Infeasible,Infeasible_set),
	chains_discard_infeasible_prefixes(Chains,Infeasible_set,chains(_,ChainsRest),Changes),
	assertion(ChainsRest=
	[
	[1],
	[2],	
	[multiple([3],[
			[1],
			[2]
			])]
	]),
	
	assertion(Changes=[
	([[4]],none),
	([[4],1],none),
	([[4],2],none),
	(
		[multiple([3],[
			[1],
			[2],
			[[4]],
			[[4],1],
			[[4],2]
			])]
		,
		[multiple([3],[
			[1],
			[2]
			])]
	)	
	]).
	
test(chains_discard_infeasible_combinations):-
	loops_example(sequence_incompatible,Loops),
	compute_chains(Loops,Chains,_),
	Chains=chains(_,Chain_list),
	assertion(Chain_list=[
	[1],
	[2],
	
	[3,1],
	[3,[4]],
	[3,[4],1],
	[3,[4],2],
	
		
	[[4]],
	[[4],1],
	[[4],2],
	
	
	[[5]],
	[[5],1],
	[[5],3,1],
	[[5],3,[4]],
	[[5],3,[4],1],
	[[5],3,[4],2]	
	]),
	compute_forward_invariants(fwd_inv(a(_,_),[]),Loops,Chains,Fwd_invs),
	compute_backward_invariants(Loops,Chains,Back_invs),
	chains_discard_infeasible_combinations(Chains,Back_invs,Fwd_invs,chains(_,Chains2),Changes),
	assertion(Chains2=[
	[1],
	[2],
	
	[3,1],
	[3,[4]],
	[3,[4],1],
	[3,[4],2],
	
		
	[[4]],
	[[4],1],
	[[4],2],
	
	[[5]],
	[[5],1],
	[[5],3,1]
	]),
	assertion(Changes=[
		([[5],3,[4]],none),
		([[5],3,[4],1],none),
		([[5],3,[4],2],none)	
	]).

test(chains_update_with_discarded_loops):-
	Chains=chains([phase([1],[]), phase([2,7],[]), phase([4,5,6],[]),phase([3],[])],
	[
	[[3]],
	[[4,5,6]],
%	[multiple([2,7],[[3],[[4,5,6]] ])]
	[multiple([1],[ [multiple([2,7],[[[3]],[[4,5,6]],[] ])] ])]
	]),
	chains_update_with_discarded_loops(Chains,[2,3,5],Chains2,Changes_map),
	Chains2=chains(Phases2,Chain_list2),
	assertion(Phases2=[phase([1],[]), phase([7],[]), phase([4,6],[])]),
	assertion(Chain_list2=
		[
		[[4,6]],
%		[multiple([7],[[[4,6]] ])]
		[multiple([1],[ [multiple([7],[[[4,6]],[] ])] ])]
		]
	),
	assertion(Changes_map=[
		([[3]],none),
		( [[4,5,6]], [[4,6]] ),
		( [multiple([1],[ [multiple([2,7],[[[3]],[[4,5,6]],[] ])] ])],  [multiple([1],[ [multiple([7],[[[4,6]],[] ])] ])]),
		(  [multiple([2,7],[[[3]],[[4,5,6]],[] ])], [multiple([7],[[[4,6]],[] ])] )		
		]
	).

test(chains_update_with_discarded_loops2):-
	Chains=chains([phase([4],[]),phase([3],[]),phase([2,5],[]),phase(1,[])],[
				[[4],multiple([3],[ [[2,5],1],[1]])]
				]),
	chains_update_with_discarded_loops(Chains,[5],_,Changes_map),
	%the map has to record all the subchains
	assertion(Changes_map=
		[	
		([[2,5],1],[[2],1]),
		([[4],multiple([3],[ [[2,5],1],[1]])],[[4],multiple([3],[ [[2],1],[1]])]),
		([multiple([3],[ [[2,5],1],[1]])],[multiple([3],[ [[2],1],[1]])])
		]).
		
test(chains_discard_terminating_non_terminating):-	
	Chains=chains([phase([1],[]), phase([2,7],[]), phase([4,5,6],[]),phase([3],[])],
		[
			[[3],1],
			[[3]],
			[[4,5,6]],
			[multiple(8,[[multiple([1],[ [multiple([2,7],[[[3]],[[4,5,6]],[] ])], [] ])]])]
		]),
	chains_discard_terminating_non_terminating(Chains,[[3],[4,5,6]],chains(_,Chain_list2),Changes),
	assertion(Chain_list2=[
		[[3],1],
		[multiple(8,[[multiple([1],[ [multiple([2,7],[ []])], [] ])]])]
		]),
	assertion(Changes=
	[
		([[3]],none),
		([[4,5,6]],none),
		(
		[multiple(8,[[multiple([1],[ [multiple([2,7],[[[3]],[[4,5,6]],[] ])], [] ])]])],
		[multiple(8,[[multiple([1],[ [multiple([2,7],[ []])], [] ])]])]
		),
		(
		[multiple([1],[ [multiple([2,7],[[[3]],[[4,5,6]],[] ])], [] ])],
		[multiple([1],[ [multiple([2,7],[ []])], [] ])]
		),
		(
		[multiple([2,7],[[[3]],[[4,5,6]],[] ])],
		[multiple([2,7],[ []])]
		)
	]),	
	chains_discard_terminating_non_terminating(Chains,[[2,7],[3],[4,5,6]],chains(_,Chain_list3),_Changes2),
	assertion(Chain_list3=[
		[[3],1],
		[multiple(8,[[multiple([1],[[] ])]])]
		]),
	chains_discard_terminating_non_terminating(Chains,[[1],[2,7],[3],[4,5,6]],chains(_,Chain_list4),_Changes3),	
	assertion(Chain_list4=[
		[[3],1]
		]).
			
:-end_tests(chains).