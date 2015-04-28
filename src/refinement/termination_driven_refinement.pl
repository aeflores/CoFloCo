:- module(termination_driven_refinement,[
		termination_driven_refinement/2
	]).
	
	
:- use_module('../ranking_functions',[init_ranking_functions/0,
				 clean_ranking_functions/1,
			     find_ranking_functions/2,
			     ranking_function/4,
			     partial_ranking_function/7,
			     unbounded_loop/2,
			     computed_ranking_functions/3
			     ]).
:- use_module('../db',[loop_ph/6,phase_loop/5,add_loop_ph/6]).
:- use_module('chains',[chain/3,phase/3]).	
:- use_module('loops',[compute_phase_loops/2]).	  	
:- use_module(chains,[compute_chains/2]).
:- use_module(stdlib(numeric_abstract_domains),[nad_project/3,nad_minimize/3,
						nad_consistent_constraints/1,
						nad_entails/3, nad_lub/6,nad_list_lub/2,
						nad_widen/5, nad_false/1,
						nad_all_ranking_functions_PR/4,
						nad_glb/3]).
:- use_module('../utils/cofloco_utils',[zip_with_op/4,
						assign_right_vars/3,
						normalize_constraint/2]).
						
max_termination_refinement_iterations(10).

termination_driven_refinement(Head,RefCnt):-
	max_termination_refinement_iterations(N),
	termination_driven_refinement_1(Head,RefCnt,N).

termination_driven_refinement_1(Head,RefCnt,0):-!,
	retractall(ranking_function(Head,_,_,_)),
	retractall(partial_ranking_function(Head,_,_,_,_,_,_)),
	retractall(computed_ranking_functions(Head,_,_)),
	find_ranking_functions(Head,RefCnt).

termination_driven_refinement_1(Head,RefCnt,N):-
	retractall(unbounded_loop(Head,_)),
	retractall(ranking_function(Head,_,_,_)),
	retractall(partial_ranking_function(Head,_,_,_,_,_,_)),
	retractall(computed_ranking_functions(Head,_,_)),
	find_ranking_functions(Head,RefCnt),
	(unbounded_loop(Head,_Loop)->
		(refine_unbounded_loops(Head,RefCnt)->
		compute_chains(Head,2),
		retractall(phase_loop(_,RefCnt,Head,_,_)),
		compute_phase_loops(Head,2),
		N1 is N-1,
		termination_driven_refinement_1(Head,RefCnt,N1)
		;
		true)
	;
	  true).

refine_unbounded_loops(Head,RefCnt):-
	unbounded_loop(Head,Loop),
	functor(Head,F,_),
	loop_ph(Head,(Loop,_),Call,Cs_loop,_,_),
	copy_term((Head,Call,Cs_loop),(Headp,Callp,Cs_loopp)),
	numbervars((Headp,Callp),0,_),
	format('loop ~p ~p is unbounded:~n ~p -> ~p ->p ~n',[F,Loop,Headp,Cs_loopp,Callp]),
	Head=..[_|Vars],
	nad_project(Vars,Cs_loop,Projected),
	get_bounded_from_below_exps(Projected,Exps),
	copy_term((Head,Exps),(Headp,Expsp)),
	format('bounded candidates ~p~n',[Expsp]),
	select_candidate(Exps,Head,Call,Cs_loop,(Positive_cond,Negative_cond)),!,	
	retract(loop_ph(Head,(Loop,RefCnt),Call,Cs_loop,Equations,Term_flag)),
	add_loop_ph(Head,RefCnt,Call,[Positive_cond|Cs_loop],Equations,Term_flag),
	assert(loop_ph(Head,(Loop,RefCnt),Call,[Negative_cond|Cs_loop],Equations,Term_flag)).

select_candidate([Exp|_More],Head,Call,Cs_loop,(Positive_conds,No_Ranking_cond)):-
	copy_term((Head,Exp),(Call,Exp_p)),	
	Head=..[_|Vars],
	Call=..[_|Vars2],
	normalize_constraint(Exp =< Exp_p,No_Ranking_cond),
	nad_project(Vars,Cs_loop,Projected),
	nad_project(Vars,[No_Ranking_cond|Cs_loop],Projected2),
	nad_project(Vars2,Cs_loop,Projected_end),
	nad_project(Vars2,[No_Ranking_cond|Cs_loop],Projected_end2),

	(
	\+nad_entails(Vars,Projected,Projected2)
	;
	\+nad_entails(Vars,Projected_end,Projected_end2)
	),!,

	copy_term((Head,Exp),(Head2,Exp_1)),
	numbervars((Head2),0,_),
	format('candidate selected: ~p~n',[Exp_1]),
	negate_condition(No_Ranking_cond,Positive_conds).
	
select_candidate([_|More],Head,Call,Cs_loop,(Positive_cond,Negative_cond)):-
	select_candidate(More,Head,Call,Cs_loop,(Positive_cond,Negative_cond)).


	
negate_condition(X>=Y,Neg):-
	normalize_constraint(X+1=<Y,Neg).
negate_condition(X=<Y,Neg):-
	normalize_constraint(X>=Y+1,Neg).
negate_condition(X=Y,[Neg,Neg2]):-
	normalize_constraint(X+1=<Y,Neg),
	normalize_constraint(X>=Y+1,Neg2).

get_bounded_from_below_exps(Exps,Exps2):-
	format('all expressions ~p~n',[Exps]),
	include(is_greater_than,Exps,Exps1),
	format('expressions ~p~n',[Exps1]),
	maplist(get_left_side,Exps1,Exps2).
is_greater_than(_ >= _).
is_greater_than(_ = _).
get_left_side(E >= C,E-C).
get_left_side(E = _,E).