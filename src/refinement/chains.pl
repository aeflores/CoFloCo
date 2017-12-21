/** <module> chains

This module computes the chains (possible patterns of execution) for a given SCC.

A chain is a sequence of phases that are executed one after another.
The sequence of phases are stored in inverse order. The head of the list is the base case
and the last element is the one executed first.

A phase can be of two kinds:
  * A simple phase X consist on a cost equation X executed once
  * An interative phase [X1,X2,...XN] consists on a set of cost equations X1,X2,...,XN that call each other a positive number of times.
    The regular expression that represents such a phase is (X1 \/ X2 \/...\/ XN)^+ where \/ is OR. 
   
  
In order to compute the chains, we infer a graph of which cost equations can call each other.
The cycles are grouped in phases and  all the possible sequences of phases are generated.
The edges of the graph are computed lazily.

We force every chain to end up in a base case (a cost equation without recursive calls). 
However, for each SCC there is a special base case that will allow us to represent non-terminating executions


@author Antonio Flores Montoya

@copyright Copyright (C) 2014,2015,2016 Antonio Flores Montoya

@license This file is part of CoFloCo. 
    CoFloCo is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    any later version.

    CoFloCo is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with CoFloCo.  If not, see <http://www.gnu.org/licenses/>.
*/


:- module(chains,[
				phase_add_property/4,
				phase_get_property/3,
				phase_set_cost/3,
				phase_get_cost/2,	
				phase_get_pattern/2,
				phase_get_rfs/2,
				phase_get_termination/2,
				phase_is_iterative/1,
					
				chain_get_pattern/2,
				chain_get_property/3,
				chains_get_chain/3,
				chain_set_cost/3,
				chain_get_cost/2,
				
				compute_chains/2,
				chains_reversed_chains/2,
				chains_discard_infeasible_prefixes/4,
				chains_discard_infeasible/4,
				chains_discard_infeasible_combinations/5,
				chains_update_with_discarded_loops/4,
				chains_discard_terminating_non_terminating/4,
				chains_annotate_termination/3
				]).


:- use_module('../utils/polyhedra_optimizations',[nad_consistent_constraints_group/2]).
:- use_module('../utils/scc_tarjan_lazy',[scc_lazy_tarjan/2]).
:- use_module(invariants,[back_invs_get/3,
						  fwd_invs_get/3]).

:- use_module(loops,[loop_is_multiple/1,
					loop_is_base_case/1,
					loop_get_property/3,
					loops_range/2,
					loops_get_list/3,
					loops_get_ids/2,
					loops_get_loop_fresh/3,
					loops_get_loop/3]).
:- use_module(stdlib(numeric_abstract_domains),[nad_consistent_constraints/1,nad_glb/3]).
:- use_module(stdlib(profiling),[profiling_start_timer/1,profiling_get_info/3,
				 profiling_stop_timer/2,profiling_stop_timer_acum/2]).
:-use_module(stdlib(set_list),[from_list_sl/2,contains_sl/2,difference_sl/3]).
:-use_module(stdlib(list_map),[empty_lm/1,lookup_lm/3,insert_lm/4]).

:-use_module(library(apply_macros)).
:-use_module(library(lists)).
:-use_module(library(lambda)).

%! chain(Head:term,RefCnt:int,Chain:chain)
% each predicate chain represent a possible pattern of execution of the SCC
% determined by Head. 
%
% [phase1,phase2,phase3] represents a chain where phase1 is executed first and
% phase3 is the base case of the recusion.
% Each phase is represented as a number if it is a non-iterative phase
% or a ordered list of numbers if it is an iterative phase.
% Each number is the id of a cost equation
%
% if phase3 is iterative, it represents a non-terminating computation
%
% a phase can also be of the form multiple(Sub-chains) where Sub-chains are a set of chain fragments.
% This phases follow other phases that contain multiple recursion 



%! compute_chains(Head:term,CntRef:int) is det
%  * erase the previous graph
%
%  * add the nodes corresponding to Head: In order to compute the chains we create a directed graph 
%    where the nodes are the cost equations id of a SCC and 
%    the edges represent the calls among the different cost equations.
%
%  * compute phases: The cost equations that appear in cycles are grouped together into phases
%
%  * compute all possible chains: The set of execution patterns is all possible sequences of phases
%

%chains(Phases,Chains)
phase_add_property(phase(Ph,Properties),Name,Val,phase(Ph,Properties2)):-
	insert_lm(Properties,Name,Val,Properties2).
	
phase_get_property(phase(_Ph,Properties),Name,Val):-
	lookup_lm(Properties,Name,Val).

phase_set_cost(Phase,Cost,Phase2):-
	phase_add_property(Phase,cost,Cost,Phase2).
	
phase_get_cost(Phase,Cost):-
	phase_get_property(Phase,cost,Cost).
	
phase_get_rfs(Phase,Rfs):-
	phase_get_property(Phase,ranking_functions,Rfs),!.
phase_get_rfs(_,ranking_functions(_,[])).		

phase_get_termination(Phase,Term_arg):-
	phase_get_property(Phase,termination,Term_arg).		
		
phase_is_terminating(Ph):-
	phase_get_property(Ph,termination,Val),
	functor(Val,terminating,_).
	
phase_is_iterative(phase([_|_],_)).

	
phase_get_pattern(phase(Ph,_),Ph).

phase_discard(Ph,Discarded,Ph2):-
	Ph=[_|_],!,
	difference_sl(Ph,Discarded,Ph2),
	Ph2\=[].

phase_discard(Ph,Discarded,Ph):-
	number(Ph),!,
	\+contains_sl(Discarded,Ph).
	
chains_update_with_discarded_loops(chains(Phases,Chains),Discarded_loops,chains(Phases2,Chains2),Changes):-
	exclude_loops_from_phase(Phases,Discarded_loops,Phases2),
	chains_transform_and_discard(Chains,[],check_discarded_loops(Discarded_loops),Chains2,[],Changes).



exclude_loops_from_phase([],_Discarded,[]).
exclude_loops_from_phase([phase(Ph,Properties)|Phases],Discarded,[phase(Ph2,Properties)|Phases1]):-
	phase_discard(Ph,Discarded,Ph2),!,
	exclude_loops_from_phase(Phases,Discarded,Phases1).
exclude_loops_from_phase([_Ph|Phases],Discarded,Phases1):-
	exclude_loops_from_phase(Phases,Discarded,Phases1).	


check_discarded_loops(_Discarded_loops,[],_,[]):-!.

check_discarded_loops(Discarded_loops,[multiple(Ph,Tails)],_,[multiple(Ph2,Tails)]):-
	phase_discard(Ph,Discarded_loops,Ph2).
	
check_discarded_loops(Discarded_loops,[Ph|Chain],_,[Ph2|Chain]):-
	phase_discard(Ph,Discarded_loops,Ph2).


chains_get_chain(chains(_,Chains),Chain_pattern,Chain):-
	once(member(chain(Chain_pattern,Properties),Chains)),
	Chain=chain(Chain_pattern,Properties).
		
	
chains_discard_infeasible_prefixes(chains(Phases,Chains),Infeasible_prefixes,chains(Phases,Chains2),Changes):-
	chains_transform_and_discard(Chains,[],check_infeasible_prefixes(Infeasible_prefixes),Chains2,[],Changes).
	

check_infeasible_prefixes(Infeasible_prefixes,Chain,Prefix,Chain):-
	\+contains_sl(Infeasible_prefixes,Prefix).
	
chains_discard_terminating_non_terminating(chains(Phases,Chains),Chains2,Changes):-
	include(phase_is_terminating,Phases,Terminating_phases),
	maplist(phase_get_pattern,Terminating_phases,Terminating_phases_pattern),
	sort(Terminating_phases_pattern,Terminating_phases_set),
	chains_discard_terminating_non_terminating(chains(Phases,Chains),Terminating_phases_set,Chains2,Changes).
			
chains_discard_terminating_non_terminating(chains(Phases,Chains),TerminatingPhases,chains(Phases,Chains2),Changes):-
	chains_transform_and_discard(Chains,[],check_terminating_non_terminating(TerminatingPhases),Chains2,[],Changes).
	
		
check_terminating_non_terminating(_TerminatingPhases,[],[Phase|_],[]):-
	number(Phase),!.
	
check_terminating_non_terminating(TerminatingPhases,[],[Phase|_],[]):-
	Phase=[_|_],!,
	\+contains_sl(TerminatingPhases,Phase).
	
check_terminating_non_terminating(_TerminatingPhases,Chain,_,Chain).


chains_discard_infeasible(chains(Phases,Chains),Infeasible_chains,chains(Phases,Chains2),Changes):-
	chains_transform_and_discard(Chains,[],check_infeasible_chains(Infeasible_chains),Chains2,[],Changes).
	
	
check_infeasible_chains(Infeasible_chains,Chain,_Prefix,Chain):-
	\+contains_sl(Infeasible_chains,Chain).

	
chains_discard_infeasible_combinations(chains(Phases,Chains),Backward_invs,Fwd_invs,chains(Phases,Chains2),Changes):-
	chains_transform_and_discard(Chains,[],check_fwd_back_combination(Backward_invs,Fwd_invs),Chains2,[],Changes).
	
	
check_fwd_back_combination(Back_invs,Fwd_invs,Chain,Prefix,Chain):-
	back_invs_get(Back_invs,Chain,inv(Head,_,InvB)),
	fwd_invs_get(Fwd_invs,Prefix,inv(Head,_,InvF)),
	nad_glb(InvB,InvF,Inv),
	nad_consistent_constraints(Inv).
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% high level predicate to discard or simplify chains according to different conditions
chains_transform_and_discard(Chains,Prefix,Check,Chains3,Changes_accum,Changes_map):-	
	foldl(\Chain^chain_transform_and_discard(Chain,Prefix,Check),Chains,([],Changes_accum),(Chains2,Changes_map)),
	reverse(Chains2,Chains3).

chain_transform_and_discard(Chain,Prefix,Check,(Accum_ch,Accum_map),([Chain2|Accum_ch],Changes_map)):-
	chain_transform(Chain,Prefix,Check,Chain2,Accum_map,Changes_map),!.

	
chain_transform_and_discard(Chain,_,_Check,(Accum_ch,Accum_map),(Accum_ch,Accum_map2)):-
	insert_lm(Accum_map,Chain,none,Accum_map2).
	


chain_transform([],Prefix,Check,[],Changes,Changes):-
	call(Check,[],Prefix,[]).
	
chain_transform([multiple(Ph,Tails)],Prefix,Check,[multiple(Ph2,Tails2)],Changes_accum,Changes_map):-!,
	call(Check,[multiple(Ph,Tails)],Prefix,[multiple(Ph2,Tails)]),
	chains_transform_and_discard(Tails,[Ph|Prefix],Check,Tails2,Changes_accum,Changes_accum2),
	Tails2\=[],
	([multiple(Ph,Tails)]\=[multiple(Ph2,Tails2)]->
		insert_lm(Changes_accum2,[multiple(Ph,Tails)],[multiple(Ph2,Tails2)],Changes_map)
		;
		Changes_map=Changes_accum2
	).

chain_transform([Ph|Chain],Prefix,Check,[Ph2|Chain2],Changes_accum,Changes_map):-
	call(Check,[Ph|Chain],Prefix,[Ph2|Chain]),
	chain_transform(Chain,[Ph|Prefix],Check,Chain2,Changes_accum,Changes_accum2),
	([Ph|Chain]\=[Ph2|Chain2]->
		insert_lm(Changes_accum2,[Ph|Chain],[Ph2|Chain2],Changes_map)
		;
		Changes_map=Changes_accum2
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
chain_add_property(chain(Chain,Properties),Name,Val,chain(Chain,Properties2)):-
	insert_lm(Properties,Name,Val,Properties2).
	
chain_get_property(chain(_Chain,Properties),Name,Val):-
	lookup_lm(Properties,Name,Val).

chain_get_pattern(chain(Chain,_),Chain).

chain_set_cost(Chain,Cost,Chain2):-
	chain_add_property(Chain,cost,Cost,Chain2).
	
chain_get_cost(Chain,Cost):-
	chain_get_property(Chain,cost,Cost).
	
	
chains_annotate_termination(Chains,Loops,Chains_annotated):-
	Chains=chains(Phases,Chain_list),
	maplist(\Chain^Chain_annot^(Chain_annot=chain(Chain,[])),Chain_list,Chain_annot_list),
	maplist(\Chain_1^Chain_2^chain_annotate_termination(Chain_1,Loops,Chain_2),Chain_annot_list,Chain_annot_list2),
	Chains_annotated=chains(Phases,Chain_annot_list2).
	
chain_annotate_termination(chain(Chain,Properties),Loops,Chain2):-
	(chain_is_non_terminating(Chain,Loops)->
		chain_add_property(chain(Chain,Properties),termination,non_terminating,Chain2)
		;
		chain_add_property(chain(Chain,Properties),termination,terminating,Chain2)
	).


chain_is_non_terminating([Phase],Loops):-
	(
	Phase=[_|_]
	;
	phase_has_divergent_loop(Phase,Loops)
	).
	
chain_is_non_terminating([multiple(Phase,Tails)],Loops):-!,
	(
	phase_has_divergent_loop(Phase,Loops)
	;
	member([],Tails)
	;
	member(Tail,Tails),
	chain_is_non_terminating(Tail,Loops)
	).

chain_is_non_terminating([Phase,Phase2|Chain],Loops):-
	(
	phase_has_divergent_loop(Phase,Loops)
	;
	chain_is_non_terminating([Phase2|Chain],Loops)
	).
	
phase_has_divergent_loop(Loop_id,Loops):-
	number(Loop_id),!,
	loops_get_loop(Loops,Loop_id,Loop),
	loop_get_property(Loop,termination,non_terminating).
	
phase_has_divergent_loop(Phase,Loops):-
	loops_get_list(Loops,Phase,Loops_list),
	member(Loop,Loops_list),
	loop_get_property(Loop,termination,non_terminating).		

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
is_multiple_phase(Phase,Loops):-
	Phase=[_|_],!,
	loops_get_list(Loops,Phase,Loops_phase),
	member(Loop,Loops_phase),
	loop_is_multiple(Loop).
is_multiple_phase(Phase,Loops):-
	number(Phase),!,
	loops_get_loop(Loops,Phase,Loop),
	loop_is_multiple(Loop).	
	
compute_chains(Loops,chains(Phases_annotated,Chains_set)):-
	loops_range(Loops,range(I,N)),
	create_unkown_graph(I,N,Graph),
	compute_phases(Loops,Graph,Phases),
	findall(Chain,
		compute_chain(Phases,[],Loops,Graph,Chain),
	Chains),
	maplist(wrap_phase(Loops),Phases,Phases_annotated),
	from_list_sl(Chains,Chains_set).

%TODO add more info about the phases
wrap_phase(_,Phase,phase(Phase,Empty_prop)):-
	empty_lm(Empty_prop).
	
compute_chain(_Phases,Chain,Loops,_Graph,Chain_rev):-
	Chain=[Last|_],
	(	Last=[_|_]
	; 
		loops_get_loop(Loops,Last,Loop),loop_is_base_case(Loop)
	),
	reverse(Chain,Chain_rev).
compute_chain(Phases,Accum,Loops,Graph,Chain):-
	member(Phase,Phases),
	(Accum=[Prev|_]->
			phase_edge(Loops,Graph,Prev,Phase)
	;
			true
	),
	discard_up_to(Phases,Phase,Rest),
	(is_multiple_phase(Phase,Loops)->
		findall(Tail,
			(
			compute_chain(Rest,[Phase],Loops,Graph,[Phase|Tail])
			), Tails),
			from_list_sl(Tails,Tails_set),
			reverse([multiple(Phase,Tails_set)|Accum],Chain)
	;
		compute_chain(Rest,[Phase|Accum],Loops,Graph,Chain)
	).
		


discard_up_to([Sel|Phases],Sel,Phases):-!.
discard_up_to([_|Phases],Sel,Phases1):-
	discard_up_to(Phases,Sel,Phases1).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

chains_reversed_chains(chains(_,Chains),Reversed_chains):-
	foldl(get_reversed_chains([]),Chains,[],Reversed_chains).

get_reversed_chains(Prefix,[multiple(Phase,Tails)],Accum,Rev_chains):-!,
	foldl(get_reversed_chains([Phase|Prefix]),Tails,Accum,Rev_chains).
	
get_reversed_chains(Prefix,[],Accum,Rev_chains):-!,
	insert_sl(Prefix,Accum,Rev_chains).
	
get_reversed_chains(Prefix,[Phase|Chain],Accum,Rev_chains):-
	get_reversed_chains([Phase|Prefix],Chain,Accum,Rev_chains).
	
	

	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


compute_phases(Loops,Graph,Phases):-
	initialize_phases(Loops,Rec_loops,Base_cases),
	Lazy_graph=lazy_graph(Rec_loops,chains:get_edge,(Loops,Graph)),
	scc_lazy_tarjan(Lazy_graph,Rec_phases),
	maplist(strip_singular_class(Lazy_graph),Rec_phases,Rec_phases2),
	append(Rec_phases2,Base_cases,Phases).

initialize_phases(Loops,Rec_phases,Base_cases):-
	loops_get_ids(Loops,Ids),
	partition(loop_is_base_case,Ids,Base_cases,Rec_phases).


strip_singular_class(lazy_graph(_,_,Info),[Loop],Loop):-
	\+get_edge(Info,Loop,Loop),!.
	
strip_singular_class(_,Phase,Phase).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% this predicates are used to check and infer edges in the graph lazily
% the idea is to compute the minimun number of edges as the computation of edges can be expensive

phase_edge(Loops,Graph,O_ph,D_ph):-
	number(O_ph),
	number(D_ph),!,
	get_edge((Loops,Graph),O_ph,D_ph).

phase_edge(_Loops,Graph,O_ph,D_ph):-
	phase_edge_cheap(Graph,O_ph,D_ph),!.
	
phase_edge(Loops,Graph,O_ph,D_ph):-
	phase_edge_expensive(Loops,Graph,O_ph,D_ph).
	
phase_edge_cheap(Graph,O_ph,D_ph):-
	(number(O_ph),O=O_ph
	;
	member(O,O_ph)
	),
	(number(D_ph),D=D_ph
	;
	member(D,D_ph)
	),
	get_unkown_graph_elem(Graph,O,D,yes),!.

phase_edge_expensive(Loops,Graph,O_ph,D_ph):-
	(number(O_ph),O=O_ph
	;
	member(O,O_ph)
	),
	(number(D_ph),D=D_ph
	;
	member(D,D_ph)),
	get_edge((Loops,Graph),O,D),!.
	

get_edge((_Loops,Graph),O,D):-
   get_unkown_graph_elem(Graph,O,D,yes),!.

get_edge((Loops,Graph),O,D):-
	get_unkown_graph_elem(Graph,O,D,unknown),
	loops_get_loop_fresh(Loops,O,loop(_Head,Calls,Phi,_)),
	loops_get_loop_fresh(Loops,D,loop(Head2,_,Phi2,_)),
    append(Phi,Phi2,Composed_cons),
   (is_edge_possible(Head2,Calls,Composed_cons)->
	    set_unkown_graph_elem(Graph,O,D,yes)
	    ;
	    set_unkown_graph_elem(Graph,O,D,no),
	    fail
	    ).

%% this can be uncommented to deactivate chain refinement (obtain a single iterative phase)
%is_edge_possible(_Head2,[_|_],_Cs):-!.

is_edge_possible(Head2,Calls,Cs):-
	member(Head2,Calls),
	Head2=..[_|Relevant_vars],
	nad_consistent_constraints_group(Relevant_vars,Cs).
	
create_unkown_graph(I,N,un_graph(I,N,Matrix)):-
	Len is N-I+1,
	make_lines(Len,Len,Lines),
	Matrix=..[matrix|Lines].
	
make_lines(0,_,[]):-!.
make_lines(N,Len,[Line|Lines]):-
	length(List,Len),
	maplist(\Elem^(Elem=unknown),List),
	Line=..[line|List],
	N1 is N-1,
	make_lines(N1,Len,Lines).
	
get_unkown_graph_elem(un_graph(I,_N,Graph),NLine,NColumn,Elem):-
	NLine1 is NLine-I+1,
	NColumn1 is NColumn-I+1,
	arg(NLine1, Graph, Line),
	arg(NColumn1,Line,Elem).
set_unkown_graph_elem(un_graph(I,_N,Graph),NLine,NColumn,Elem):-
	NLine1 is NLine-I+1,
	NColumn1 is NColumn-I+1,
	arg(NLine1, Graph, Line),
	nb_setarg(NColumn1,Line,Elem).	
