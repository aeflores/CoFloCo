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

@copyright Copyright (C) 2014,2015 Antonio Flores Montoya

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


:- module(chains,[compute_chains/2,chain/3,phase/3,init_chains/0]).


:- use_module('../db',[loop_ph/6]).

:- use_module('../utils/cofloco_utils',[assign_right_vars/3]).
:- use_module('../utils/polyhedra_optimizations',[nad_consistent_constraints_group/2]).

:- use_module(stdlib(numeric_abstract_domains),[nad_project/3,nad_consistent_constraints/1, nad_entails/3, nad_lub/6, nad_widen/5,nad_glb/3]).
:- use_module(stdlib(utils),[ut_remove/3]).
:- use_module(stdlib(multiset),[empty_ms/1,add_ms/3,add_list_ms/3]).
:- use_module(stdlib(set_list)).
:- use_module(stdlib(list_utils),[take_lu/3]).
:- use_module(stdlib(profiling),[profiling_start_timer/1,profiling_get_info/3,
				 profiling_stop_timer/2,profiling_stop_timer_acum/2]).
	
%! chain(Head:term,RefCnt:int,Chain:chain)
% each predicate chain represent a possible pattern of execution of the SCC
% determined by Head. 
%
% [phase1,phase2,phase3] represents a chain where phase3 is executed first and
% phase1 is the base case of the recusion.
% Each phase is represented as a number if it is a non-iterative phase
% or a ordered list of numbers if it is an iterative phase.
% Each number is the id of a cost equation
%
% @arg RefCnt represents the refinement phase to which the chain belongs
% @arg Chain is a list of loop phases in inverse order
:- dynamic  chain/3.

%! node(Id:equation_id,Type:atom)
% a node of the graph that is being inferred
% @Type can be final (if it's a base case) or loop (if it's a recursive equation)
:- dynamic  node/2.

%! edge(S:equation_id,D:equation_id)
% there is an edge from S to D
:- dynamic  edge/2.

%! not_edge(S:equation_id,D:equation_id)
% there is NOT an edge from S to D
% this is necessary because of the lazy computation (abscence of edge does not mean not_edge)
:- dynamic  not_edge/2.

%! phases_edge(S:Phase,D:Phase)
% there is an edge from phase S to phase D
:- dynamic  phases_edge/2.

%! not_phases_edge(S:Phase,D:Phase)
% there is NOT an edge from phase S to phase D
:- dynamic  not_phases_edge/2.

%! phase(Phase:phase,Head:term,CntRef:int)
% store a phase Phase in SCC Head in the refinement phase CntRef
:- dynamic  phase/3.

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
%  * remove imposible chains generated with the non_terminating_stub/2
compute_chains(Head,RefCnt):-
	clean_graph,
	retractall(chain(Head,RefCnt,_)),
	retractall(phase(_,Head,RefCnt)),
	add_nodes(Head,RefCnt),
	compute_phases(Head,RefCnt),
	compute_basic_chains(Head,RefCnt),
	compute_rec_chains(Head,RefCnt),
	remove_impossible_non_terminating_chains(Head,RefCnt).

%! init_chains is det
%  erase all chains and phases
init_chains:-
	retractall(phase(_,_,_)),
	retractall(chain(_,_,_)).

clean_graph:-
	 retractall(node(_,_)),
	 retractall(edge(_,_)),
	 retractall(not_edge(_,_)),
	 retractall(phases_edge(_,_)),
	 retractall(not_phases_edge(_,_)).


add_nodes(Head,RefCnt):-	 
	loop_ph(Head,(Id_Loop,RefCnt),Call,_,_,_),
	(Call==none->
	  assert(node(Id_Loop,final))
	  ;
	  assert(node(Id_Loop,loop))
	  ),
	fail.
add_nodes(_,_).	

%! remove_impossible_non_terminating_chains(+Head:term,+RefCnt:int) is det
% A non_terminating_stub is an empty loop used to generate chains that represent non-terminating executions.
% If X is a non_terminating_stub a chain [X,P1,P2...PN] represents an execution where P1 goes on forever.
%
% this predicate remove chains that do not make sense such as [X] and [X,PI...] where PI is not an iterative phase.
remove_impossible_non_terminating_chains(Head,RefCnt):-
	chain(Head,RefCnt,Chain),
	is_impossible_non_terminating(Head,Chain),
	retract(chain(Head,RefCnt,Chain)),
	fail.
remove_impossible_non_terminating_chains(_,_).


is_impossible_non_terminating(Head,[X]):-
	loop_ph(Head,(X,_RefCnt),_,_,[],non_terminating).%it is really a stub, not a non-terminating call
is_impossible_non_terminating(Head,[X,Y|_]):-
	loop_ph(Head,(X,_RefCnt),_,_,[],non_terminating),
	number(Y).


%! get_phases_edge(?C1:phase,?C2:phase) is semidet    
%  succeeds if there is an edge from C1 to C2.
% the edges are not necessarily computed, they are computed on demand (lazily)
get_phases_edge(C1,C2):-
	phases_edge(C1,C2).
	

get_phases_edge(C1,C2):-
	\+not_phases_edge(C1,C2),
	\+phases_edge(C1,C2),
	phase(C1,_,_),
	phase(C2,_,_),
	get_phases_aux(C1,C2).

get_phases_aux([C1|C1s],[C2|C2s]):-!,
     (get_one_edge_form_list_to_list([C1|C1s],[C2|C2s],_,_)->
        assert(phases_edge([C1|C1s],[C2|C2s])),
        assert(not_phases_edge([C2|C2s],[C1|C1s]))
        ;
          assert(not_phases_edge([C1|C1s],[C2|C2s])),
        fail
        ).
get_phases_aux([C1|C1s],C2):-
     number(C2),!,	
     (get_one_edge_form_list([C1|C1s],C2,_)->
        assert(phases_edge([C1|C1s],C2)),
        assert(not_phases_edge(C2,[C1|C1s]))
        ;
          assert(not_phases_edge([C1|C1s],C2)),
        fail
        ).       
get_phases_aux(C1,[C2|C2s]):-
     number(C1),!,	
     (get_one_edge_to_list(C1,[C2|C2s],_)->
        assert(phases_edge(C1,[C2|C2s])),
        assert(not_phases_edge([C2|C2s],C1))
        ;
          assert(not_phases_edge(C1,[C2|C2s])),
        fail
        ).       
get_phases_aux(C1,C2):-
     number(C1),number(C2),
     (get_edge(C1,C2)->
        assert(phases_edge(C1,C2)),
        assert(not_phases_edge(C2,C1))
        ;
          assert(not_phases_edge(C1,C2)),
        fail
        ).      

%! compute_basic_chains(+Head:term,+RefCnt:int) is det
% store the chains that are simply a base case   
compute_basic_chains(Head,RefCnt):-
	node(Id,final),
	save_chain(Head,RefCnt,[Id]),
	fail.
compute_basic_chains(_,_).

%! compute_rec_chains(+Head:term,+RefCnt:int) is det
% compute and store chains that are composed of at least two phases
compute_rec_chains(Head,RefCnt):-
	findall(Phase,phase(Phase,Head,RefCnt),Phasees),
	member(Phase,Phasees),
	delete(Phasees,Phase,Rest),
	compute_rec_chains_aux([Phase],Rest,Head,RefCnt).
compute_rec_chains(_,_).

compute_rec_chains_aux([Loop|Other],Rest,Head,RefCnt):-
	member(Phase2,Rest),
	get_phases_edge(Loop,Phase2),
	((number(Phase2),node(Phase2,final))->
	  save_chain(Head,RefCnt,[Phase2,Loop|Other]),
	  fail
	;
	delete(Rest,Phase2,Rest2),
	compute_rec_chains_aux([Phase2,Loop|Other],Rest2,Head,RefCnt)
	).



save_chain(Head,RefCnt,Chain):-
	chain(Head,RefCnt,Chain),!.
save_chain(Head,RefCnt,Chain):-
	%format('~p~n',chain(Head,RefCnt,Chain)),
	assert(chain(Head,RefCnt,Chain)).

	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% this predicates are used to check and infer edges in the graph lazily
% the idea is to compute the minimun number of edges as the computation of edges can be expensive


get_one_edge_to_list(O,D_list,D):-
   member(D,D_list),
   get_edge(O,D),!.
   
get_one_edge_form_list(O_list,D,O):-
   member(O,O_list),
   get_edge(O,D),!. 
   
get_one_edge_form_list_to_list(O_list,D_list,O,D):-
   member(O,O_list),
   member(D,D_list),
   get_edge(O,D),!.     
    
get_edges_not_to(O,D_list,D):-
	findall(N,node(N,loop),Nodes),
	from_list_sl(Nodes,Nodes_set),
	from_list_sl(D_list,D_set),
	difference_sl(Nodes_set,D_set,D_Rest),
	member(D,D_Rest),
	get_edge(O,D).
   

get_edge(O,D):-
   edge(O,D).

get_edge(O,D):-
   node(O,loop),
   node(D,_),
    \+edge(O,D),
   \+not_edge(O,D),
   loop_ph(_Head,(O,RefCnt),Head2,Phi,_,_),
   loop_ph(Head2,(D,RefCnt),_,Phi2,_,_),
    append(Phi,Phi2,Composed_cons),
	Head2=..[_|Relevant_vars],
	(nad_consistent_constraints_group(Relevant_vars,Composed_cons)->
	    assert(edge(O,D))
	    ;
	    assert(not_edge(O,D)),fail
	    ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dynamic phases_changed/0.

 
%! compute_rec_chains(+Head:term,+RefCnt:int) is det
% computes the phases of a SCC.
% starts by having a phase for each cost equations and looks for  cycles in a fixpoint computation
compute_phases(Head,RefCnt):-
	retractall(phase(_,Head,RefCnt)),
	initialize_phases(Head,RefCnt),
	phases_fixpoint(Head,RefCnt),
	strip_singular_classes(Head,RefCnt).

%! strip_singular_classes(+Head:term,+RefCnt:int) is det
%the phases that are a single cost equation that does not have an edge to itself are non-iterative
% so they are not represented as a list but rather a single cost equation id
strip_singular_classes(Head,RefCnt):-
	phase([Loop],Head,RefCnt),
	\+get_edge(Loop,Loop),
	retract(phase([Loop],Head,RefCnt)),
	assert(phase(Loop,Head,RefCnt)),
	fail.
strip_singular_classes(Head,RefCnt):-
	node(Final,final),
	save_phase(Final,Head,RefCnt),
	fail.
strip_singular_classes(_,_).


initialize_phases(Head,RefCnt):-
	node(Id_Loop,loop),
	save_phase([Id_Loop],Head,RefCnt),
	fail.
initialize_phases(_,_).

save_phase(Phase,Head,RefCnt):-
	phase(Phase,Head,RefCnt),!.
save_phase(Phase,Head,RefCnt):-
	assertz(phase(Phase,Head,RefCnt)).

phases_fixpoint(Head,RefCnt):-
	explore_phases(Head,RefCnt).
	
phases_fixpoint(Head,RefCnt):-
        retract(phases_changed),
	phases_fixpoint(Head,RefCnt).
phases_fixpoint(_Head,_RefCnt).

explore_phases(Head,RefCnt):-
	phase(Phase,Head,RefCnt),
	explore_phases_cycles([Phase]),
	phases_changed,!,
	fail.

%special case for short cycles
explore_phases_cycles([Last,Prev1|_Prev]):-
	get_one_edge_form_list_to_list(Last,Prev1,_,_),
	fussion_classes([Last,Prev1]),!.

explore_phases_cycles([Last|Prev]):-
	member(Loop,Last),
	get_edges_not_to(Loop,Last,Loop2),
	%get_edge(Loop,Loop2),
	get_phase(Loop2,Phase2),
	%Phase2\=Last,
	
	(nth1(I,[Last|Prev],Phase2)->
	         take_lu(I,[Last|Prev],Cycle),
	         fussion_classes(Cycle),!
	;
	   explore_phases_cycles([Phase2,Last|Prev])
	).
	

get_phase(Loop,Loop):-
	phase(Loop,_,_),!.
get_phase(Loop,Phase):-
	phase(Phase,_,_),
	member(Loop,Phase),!.
fussion_classes(List_classes):-
	fussion_classes_1(List_classes,[],_,_).

fussion_classes_1([],New_class,Head,RefCnt):-
	save_phase(New_class,Head,RefCnt),
	(\+phases_changed->assert(phases_changed);true).
fussion_classes_1([Phase|More],Acum,Head,RefCnt):-
	retract(phase(Phase,Head,RefCnt)),
	union_sl(Phase,Acum,Acum2),
	fussion_classes_1(More,Acum2,Head,RefCnt).

