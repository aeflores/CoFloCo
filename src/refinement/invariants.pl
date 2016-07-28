/** <module> invariants

This module computes different kinds of invariants for the chains:


  * backward_invariant/4: An invariant that relates the variables of the head of a cost equation and is computed
    backwards, form the base case of the chain to the first phase. This invariant reflects the input-output relation
    and the necessary conditions for a chain to be called
  * forward_invariant/4: An invariant that relates the variables of the head of a cost equation and is computed
    forwards, form the first phase up  to the base case. This invariant propagates any precodition we might have
    and also information from the first phases to later phases
  * scc_forward_invariant/3: This invariant reflects the preconditions of a SCC.
    It is inferred in base of all the calls to such SCC.
    In the future we could consider multiple invariants scc_forward_invariant/3, one for each call to the SCC
    to increase precission
  * phase_transitive_closure/5:  The transitive closure of a phase
  
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

:- module(invariants,[compute_invariants_for_scc/2,
		      compute_forward_invariants/2,
		      clean_invariants/0,
		      add_backward_invariant/3,
		      backward_invariant/4,
		      partial_backward_invariant/5,
		      context_insensitive_backward_invariant/3,
		      forward_invariant/4,
		      context_insensitive_forward_invariant/3,
		      scc_forward_invariant/3,
		      phase_transitive_closure/5,
		      phase_transitive_star_closure/5,
		      add_scc_forward_invariant/3]).

:- use_module('../db',[loop_ph/6,phase_loop/5]).
:- use_module(chains,[chain/3,get_reversed_chains/3]).
:- use_module(loops,[split_multiple_loops/2]).

:- use_module('../utils/cofloco_utils',[assign_right_vars/3,zip_with_op2/4,zip_with_op2/4,ground_copy/2]).
:- use_module('../utils/polyhedra_optimizations',[nad_project_group/3,
					nad_consistent_constraints_group_aux/1,
					nad_is_bottom/1,
					group_relevant_vars/4,
					nad_normalize_polyhedron/2]).
:- use_module('../utils/polyhedra_optimizations').	
:- use_module(stdlib(set_list)).
:- use_module(stdlib(counters),[counter_increase/3]).
:- use_module(stdlib(numeric_abstract_domains),[
	nad_glb/3,nad_list_glb/2,nad_project/3, nad_entails/3, nad_lub/6,nad_list_lub/2, nad_widen/5,
	nad_normalize/2,
	nad_false/1,nad_consistent_constraints/1]).
:- use_module(stdlib(utils),[ut_append/3,ut_flat_list/2, ut_member/2, ut_list_to_dlist/2,ut_split_at_pos/4]).
:- use_module(stdlib(profiling),[profiling_start_timer/1,profiling_stop_timer_acum/2]).

:- use_module(stdlib(polyhedra_ppl)).
:- use_module(stdlib(numvars_util),[to_numbervars_nu/4]).

:-use_module(library(apply_macros)).
:-use_module(library(lists)).
:-use_module(library(terms)).
%! backward_invariant(Head:term,Chain_RefCnt:(chain,int),Hash:int,Inv:polyhedron)
% An invariant that relates the variables of the head of a cost equation and is computed
%  backwards, form the base case of the chain to the first phase. This invariant reflects the input-output relation
%  and the necessary conditions for a chain to be called.
%  There is one invariant for each chain.
%
% Inv is expressed in terms of the variables of Head
:- dynamic backward_invariant/4.
  
%! forward_invariant(Head:term,Chain_RefCnt:(chain,int),Hash:int,Inv:polyhedron)
% An invariant that relates the variables of the head of a cost equation and is computed
% forwards, form the first phase up  to the base case. This invariant propagates any precodition we might have
% and also information from the first phases to later phases. 
% There is an invariant for each suffix of each chain.
%
% Inv is expressed in terms of the variables of Head
:- dynamic forward_invariant/4.
  
%! scc_forward_invariant(Head:term,RefCnt:int,Inv:polyhedron)
% This invariant reflects the preconditions of a SCC.
% It is inferred in base of all the calls to such SCC.
:- dynamic scc_forward_invariant/3.

%! phase_transitive_closure(Phase:phase,RefCnt:int,Head:term,Call:term,Inv:polyhedron)
% The transitive closure of a Phase 
%
% Inv is expressed in terms of the variables of Head and Call
:- dynamic  phase_transitive_closure/5.

%! phase_transitive_star_closure(Phase:phase,RefCnt:int,Head:term,Call:term,Inv:polyhedron)
% The transitive reflexive closure of a Phase 
%
% Inv is expressed in terms of the variables of Head and Call
:- dynamic  phase_transitive_star_closure/5.


context_insensitive_backward_invariant(Head,Phase,Backward_invariant):-
	bagof(Back_inv_star,	
	   Back_inv^Chain2^Fwd_inv^partial_backward_invariant([Phase|Chain2],Head,Fwd_inv,Back_inv,Back_inv_star),
	       Back_invs),
	nad_list_lub(Back_invs,Backward_invariant).

context_insensitive_forward_invariant(Head,Phase,Forward_invariant):-
	bagof(Fwd_inv,	
	   Hash_fwd_inv^Chain_rev2^RefCnt^forward_invariant(Head,([Phase|Chain_rev2],RefCnt),Hash_fwd_inv,Fwd_inv),
	       Fwd_invs),	
	nad_list_lub(Fwd_invs,Forward_invariant).

%! widening_frequency(-N:int) is det
% how often widening is performed
widening_frequency(1).

%! clean_invariants
% remove all the invariants from the database
clean_invariants:-
	retractall(phase_transitive_closure(_,_,_,_,_)),
	retractall(phase_transitive_star_closure(_,_,_,_,_)),
	retractall(backward_invariant(_,_,_,_)),
	retractall(forward_invariant(_,_,_,_)),
	retractall(scc_forward_invariant(_,_,_)).


%! add_backward_invariant(+Head:term,+Chain_RefCnt:(chain,int),+Inv:polyhedron)
%  store a backward invariant if it does not already exits
%  we compute the hash of the ground version of the invariant
add_backward_invariant(Head,(Chain,RefCnt),_):-
	backward_invariant(Head,(Chain,RefCnt),_,_),!.

add_backward_invariant(Head,(Chain,RefCnt),Inv):-
	copy_term((Head,Inv),(E,EPat)),
	numbervars(E,0,_),
	term_hash(EPat,Hash),
	assertz(backward_invariant(Head,(Chain,RefCnt),Hash,Inv)).
	
%! add_forward_invariant(+Head:term,+Chain_RefCnt:(chain,int),+Inv:polyhedron)
%  store a forward invariant if it does not already exits
%  we compute the hash of the ground version of the invariant
add_forward_invariant(Head,(Chain,RefCnt),_):-
	forward_invariant(Head,(Chain,RefCnt),_,_),!.
add_forward_invariant(Head,(Chain,RefCnt),Inv):-
	nad_normalize_polyhedron(Inv,Inv_normalized),
	copy_term((Head,Inv_normalized),(E,IPat)),
	numbervars(E,0,_),
	term_hash(IPat,Hash),
	assertz(forward_invariant(Head,(Chain,RefCnt),Hash,Inv_normalized)).

%! add_scc_forward_invariant(+Phase:phase,+RefCnt:int,+Inv:polyhedron)
%  store the invariant if it does not already exits
add_scc_forward_invariant(Head,RefCnt,_) :-
	scc_forward_invariant(Head,RefCnt,_),!.
add_scc_forward_invariant(Head,RefCnt,Inv) :-
	nad_normalize_polyhedron(Inv,Inv_normalized),
	assertz(scc_forward_invariant(Head,RefCnt,Inv_normalized)).
	
%! add_phase_transitive_closure(+Phase:phase,+RefCnt:int,+Head:term,+Call:term,+Inv:polyhedron)
%  store the transitive closure if it does not already exits
add_phase_transitive_closure(Phase,RefCnt,_,_,_) :-
	phase_transitive_closure(Phase,RefCnt,_,_,_),!.

add_phase_transitive_closure(Phase,RefCnt,Head,Call,Inv) :-
	assertz(phase_transitive_closure(Phase,RefCnt,Head,Call,Inv)).
	
%! add_phase_transitive_closure(+Phase:phase,+RefCnt:int,+Head:term,+Call:term,+Inv:polyhedron)
%  store the transitive closure if it does not already exits
add_phase_transitive_star_closure(Phase,RefCnt,_,_,_) :-
	phase_transitive_star_closure(Phase,RefCnt,_,_,_),!.

add_phase_transitive_star_closure(Phase,RefCnt,Head,Call,Inv) :-
	assertz(phase_transitive_star_closure(Phase,RefCnt,Head,Call,Inv)).	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! compute_invariants_for_scc(+Head:term,+RefCnt:int) is det
%  * Compute backward invariants
%  * Compute loop trasitive closures
%  * Compute relation2entry_invariants
% 
%  @throws invariants_failed This means there is a bug in the implementation
compute_invariants_for_scc(Head,RefCnt) :-
	profiling_start_timer(inv_back),
	compute_backward_invariants(Head,RefCnt),
	profiling_stop_timer_acum(inv_back,_),
	profiling_start_timer(inv_transitive),
	compute_loops_transitive_closures(Head,RefCnt),
	profiling_stop_timer_acum(inv_transitive,_),
	!. 

compute_invariants_for_scc(_N,_) :-
	throw(purs_err(invariants_failed,compute_invariants/0,[])).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%




%! partial_backward_invariant(Chain:chain,Head:term,Hash_forward_inv:(int,polyhedron),InvPlus:polyhedron,InvStar:polyhedron)
% This is a cacheing mechanism to increase performance. many chains have a common 
% prefix and that can be used to avoid redundant computations.
%
% partial_backward_invariant stores the backward invariant of a fragment of chain Chain
% because the backward invariant might depend  on the forward invariants, it contains the 
% forward invariant that was used. 
% Any chain that has Chain as a prefix and has the same forward invariant Hash_forward_inv will have the same backward invariant
% InvPlus is with 1 or more iterations
% InvStar is with 0 or more iterations
:-dynamic partial_backward_invariant/5.



%! compute_backward_invariants(+Head:term,+RefCnt:int) is det
% for each chain, try to compute the backward invariant.
% if it fails it is because it is not feasible and we can discard the chain
% otherwise we store the invariant
compute_backward_invariants(Head,RefCnt):-
    chain(Head,RefCnt,Chain),
    (compute_backward_invariant(Chain,[],Head,RefCnt,Entry_pattern)->
    add_backward_invariant(Head,(Chain,RefCnt),Entry_pattern)
    ;
    retract(chains:chain(Head,RefCnt,Chain))
    ),
    fail.
compute_backward_invariants(_,_).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%5


%! compute_backward_invariant(+Chain:chain,+Prev_chain:chain,+Head:term,+RefCnt:int,-Entry_pattern:polyhedron) is semidet
% compute the backward invariant of the chain prefix Chain knowing that the rest of the chain is Prev_chain.
% if at any point the invariant is unfeasible (bottom) the predicate fails to indicate that the chain can be removed.

% the case where the invariant is already computed
compute_backward_invariant([Ph|Chain],Prev_chain,Head,RefCnt,Entry_pattern):-%
    (Ph=multiple(Intern_ph,_)->
    forward_invariant(Head,([Intern_ph|Prev_chain],RefCnt),Hash_local_inv,Local_inv)
    ;
	forward_invariant(Head,([Ph|Prev_chain],RefCnt),Hash_local_inv,Local_inv)
	),
    partial_backward_invariant([Ph|Chain],Head,(Hash_local_inv,Local_inv2),Entry_pattern,_),
    Local_inv==Local_inv2,!,
    counter_increase(compressed_invs,1,_),
    Entry_pattern\==[0=1].

% the base case of the chain, the backward invariant is the cost equation definition
% and the corresponding forward invariant
compute_backward_invariant([Base_case],Prev_chain,Head,RefCnt,Entry_pattern_normalized):-
	number(Base_case),!,
    loop_ph(Head,(Base_case,RefCnt),[],Cs_1,_,_),
    forward_invariant(Head,([Base_case|Prev_chain],RefCnt),_Hash,Inv),
   % append(Cs_1,Inv,Cs),
    nad_glb(Cs_1,Inv,Entry_pattern),
	\+nad_is_bottom(Entry_pattern),
	nad_normalize_polyhedron(Entry_pattern,Entry_pattern_normalized).
	
% the non-terminating case, the cost relations have to be applicable, but that is all we know
compute_backward_invariant([Non_terminating],Prev_chain,Head,RefCnt,Entry_pattern):-
	Non_terminating=[_|_],!,
	phase_loop(Non_terminating,RefCnt,Head,_,Cs),
	Head=..[_|EVars],
 	nad_project_group(EVars,Cs,Entry_pattern),
 	forward_invariant(Head,([Non_terminating|Prev_chain],RefCnt),Hash_local_inv,Local_inv),
 	assertz(partial_backward_invariant([Non_terminating],Head,(Hash_local_inv,Local_inv),Entry_pattern,Entry_pattern)).

compute_backward_invariant([multiple(Non_terminating,Tails)],Prev_chain,Head,RefCnt,Entry_pattern):-
	member([],Tails),!,
	phase_loop(Non_terminating,RefCnt,Head,_,Cs),
	Head=..[_|EVars],
 	nad_project_group(EVars,Cs,Entry_pattern),
 	forward_invariant(Head,([Non_terminating|Prev_chain],RefCnt),Hash_local_inv,Local_inv),
 	assertz(partial_backward_invariant([multiple(Non_terminating,Tails)],Head,(Hash_local_inv,Local_inv),Entry_pattern,Entry_pattern)).



 % We have a phase that is not iterative (Ph is a number).
 % The backward invariant is obtained by applying the loop definition once to the
 % backward invariant of the rest of the chain
compute_backward_invariant([Ph|Chain],Prev_chain,Head,RefCnt,Entry_pattern_normalized):-
	number(Ph),!,
	copy_term(Head,Call),
	compute_backward_invariant(Chain,[Ph|Prev_chain],Call,RefCnt,Initial_inv),
	loop_ph(Head,(Ph,RefCnt),[Call],Cs,_,_),
	forward_invariant(Head,([Ph|Prev_chain],RefCnt),Hash_local_inv,Local_inv),
	Head=..[_|EVars],
	%ut_flat_list([Local_inv,Cs,Initial_inv],Cs_2),
	nad_list_glb([Local_inv,Cs,Initial_inv],Cs_2),
	nad_project_group(EVars,Cs_2,Entry_pattern),
	%even if the invariant is unfeasible, we store to save time when computing invariants with the same suffix
	nad_normalize_polyhedron(Entry_pattern,Entry_pattern_normalized),
	(nad_is_bottom(Entry_pattern_normalized)->
	  assertz(partial_backward_invariant([Ph|Chain],Head,(Hash_local_inv,Local_inv),[0=1],Initial_inv)),
	  fail
	;
	  assertz(partial_backward_invariant([Ph|Chain],Head,(Hash_local_inv,Local_inv),Entry_pattern_normalized,Initial_inv))
	  ).

% We have an iterative phase.
% we apply the loops of the phase to the backward invariant of the rest of the chain
% a number of times until we reach a fixpoint
compute_backward_invariant([Ph|Chain],Prev_chain,Head,RefCnt,Entry_pattern_normalized):-
	compute_backward_invariant(Chain,[Ph|Prev_chain],Head,RefCnt,Initial_inv),
	phase_loop(Ph,RefCnt,Head,_,Cs),
	forward_invariant(Head_loop,([Ph|Prev_chain],RefCnt),Hash_local_inv,Local_inv),
	findall((Head_loop,Call_loop,Cs_1),
	    (
	    member(Loop,Ph),
	    loop_ph(Head_loop,(Loop,RefCnt),[Call_loop],Cs_loop,_,_),
	    nad_glb(Local_inv,Cs_loop,Cs_1)
	    ),Loops),
	backward_invariant_fixpoint(inv(Head,Initial_inv),Loops,inv(Head_out,It_pattern),inv(Head_out,It_pattern_star)),
	Head=..[_|EVars],
	Head=Head_out,
	nad_project_group(EVars,Cs,Extra_conds),
	nad_glb(Extra_conds,It_pattern,Entry_pattern),
	Head=Head_loop,
	nad_normalize_polyhedron(Entry_pattern,Entry_pattern_normalized),
	nad_normalize_polyhedron(It_pattern_star,Entry_pattern_star_normalized),
	(nad_is_bottom(Entry_pattern_normalized)->
	assertz(partial_backward_invariant([Ph|Chain],Head,(Hash_local_inv,Local_inv),[0=1],Entry_pattern_star_normalized)),
	fail
	;
	assertz(partial_backward_invariant([Ph|Chain],Head,(Hash_local_inv,Local_inv),Entry_pattern_normalized,Entry_pattern_star_normalized))
	).
	
%multiple recursion phase
compute_backward_invariant([multiple(Ph,Tails)],Prev_chain,Head,RefCnt,Entry_pattern_normalized):-
	number(Ph),!,
	maplist(compute_backward_invariant_aux([Ph|Prev_chain],Head,RefCnt),Tails,Call_patterns),
	nad_list_lub(Call_patterns,Initial_inv),
    forward_invariant(Head_loop,([Ph|Prev_chain],RefCnt),Hash_local_inv,Local_inv),
	findall((Head_loop,Calls_loop,Cs_1),
	    (
	    loop_ph(Head_loop,(Ph,RefCnt),Calls_loop,Cs_loop,_,_),
	    nad_glb(Local_inv,Cs_loop,Cs_1)
	    ),Loops),
	backward_invariant_once(inv(Head,Initial_inv),Loops,inv(Head_out,Entry_pattern)),
	Head=Head_out,
	Head=Head_loop,
	nad_normalize_polyhedron(Entry_pattern,Entry_pattern_normalized),
	(nad_is_bottom(Entry_pattern_normalized)->
	assertz(partial_backward_invariant([multiple(Ph,Tails)],Head,(Hash_local_inv,Local_inv),[0=1],Initial_inv)),
	fail
	;
	assertz(partial_backward_invariant([multiple(Ph,Tails)],Head,(Hash_local_inv,Local_inv),Entry_pattern_normalized,Initial_inv))
	).


%multiple recursion phase
compute_backward_invariant([multiple(Ph,Tails)],Prev_chain,Head,RefCnt,Entry_pattern_normalized):-
	phase_loop(Ph,RefCnt,Head,_,Cs),
	maplist(compute_backward_invariant_aux([Ph|Prev_chain],Head,RefCnt),Tails,Call_patterns),
	nad_list_lub(Call_patterns,Initial_inv),
    forward_invariant(Head_loop,([Ph|Prev_chain],RefCnt),Hash_local_inv,Local_inv),
	findall((Head_loop,Calls_loop,Cs_loop),
	    (
	    member(Loop,Ph),
	    loop_ph(Head_loop,(Loop,RefCnt),Calls_loop,Cs_loop,_,_)
%	    nad_glb(Local_inv,Cs_loop,Cs_1)
	    ),Loops),    
	%backward_invariant_fixpoint(inv(Head,Initial_inv),Loops,inv(Head_out,It_pattern)),
	backward_invariant_fixpoint(inv(Head,Initial_inv),Loops,inv(Head_out,It_pattern),inv(Head_out,It_pattern_star)),
	Head=..[_|EVars],
	Head=Head_out,
	nad_project_group(EVars,Cs,Extra_conds),
	nad_glb(Extra_conds,It_pattern,Entry_pattern),
	Head=Head_loop,
	nad_normalize_polyhedron(Entry_pattern,Entry_pattern_normalized),
	nad_normalize_polyhedron(It_pattern_star,Entry_pattern_star_normalized),
	(nad_is_bottom(Entry_pattern_normalized)->
	assertz(partial_backward_invariant([multiple(Ph,Tails)],Head,(Hash_local_inv,Local_inv),[0=1],Entry_pattern_star_normalized)),
	fail
	;
	assertz(partial_backward_invariant([multiple(Ph,Tails)],Head,(Hash_local_inv,Local_inv),Entry_pattern_normalized,Entry_pattern_star_normalized))
	).
	
compute_backward_invariant_aux(Prev_chain,Head,RefCnt,Chain,Entry_pattern):-
	(compute_backward_invariant(Chain,Prev_chain,Head,RefCnt,Entry_pattern)->
		true
		;
		Entry_pattern=[0=1]
	).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	

%! unfeasible_chain_suffix(Head:term,RefCnt:int,Chain_suffix:chain)
% store suffixes of chains that are not feasible in order to avoid repeating computation of invariants
% that are going to fail.
:-dynamic unfeasible_chain_prefix/3.

%! compute_forward_invariants(Entry_Call:term,RefCnt:int) is det
% for each chain, if none of the suffixes is clearly unfeasible (because we computed it before)
% we try to compute the forward invariant.
% if we fail to compute it, then we remove the chain.
% if we don't fail, we do nothing and the chain is not removed.
compute_forward_invariants(Entry_Call,RefCnt):-
	chain(Entry_Call,RefCnt,Chain),
	get_reversed_chains([],Chain,Chains_rev),
	include(compute_prefix_forward_invariant(RefCnt,Entry_Call),Chains_rev,Feasible_prefixes),
	(Feasible_prefixes=[]->
	   retract(chains:chain(Entry_Call,RefCnt,Chain))
	   ;
	   true
	),
	fail.
compute_forward_invariants(_,_).

	
compute_prefix_forward_invariant(RefCnt,Entry_Call,Chain_prefix):-
	\+has_infeasible_prefix(Entry_Call,RefCnt,Chain_prefix),
	compute_forward_invariant(Chain_prefix,RefCnt,Entry_Call,_).	
	
has_infeasible_prefix(Entry_Call,RefCnt,Chain):-
	unfeasible_chain_prefix(Entry_Call,RefCnt,Chain_suffix),
	append(_,Chain_suffix,Chain),!.


%! compute_forward_invariant(+Chain:chain,+RefCnt:int,?Entry_Call:term,-Inv:inv(term,term,polyhedron)) is det
% given a chain fragment [P1,P2...PN], computes a invariant about the variables at any point during P1.
% This invariant is stored, but the invariant returned is a different one.
% The returned invariant is valid at any point after at least ONE iteration of P1 has been performed.
compute_forward_invariant(Chain,RefCnt,Entry_Call,Inv):-
	% This is the case when the forward invariant has already been computed
	Chain=[Not_number|_],
	\+number(Not_number),
	forward_invariant(Entry_Call,(Chain,RefCnt),_Hash,Inv),!.

%initial phase of a bigger chain not recursive
% we start from the precondition (scc_forward_invariant) and store that invariant
% then we apply the loop of the phase once and return that one
compute_forward_invariant([],_,Head, Inv):-
	scc_forward_invariant(Head,_,Inv).


%non-iterative phase
% start from the returned invariant of the suffix chain, store that invariant
% and apply the loops once to obtain the return invariant
compute_forward_invariant([Non_loop|Chain],RefCnt,Entry_Call,Inv_out):-
    number(Non_loop),!,
    compute_forward_invariant(Chain,RefCnt,Entry_Call,Inv_aux), 
          findall((Head_loop,Calls_loop,Cs_loop),
	    (
	    loop_ph(Head_loop,(Non_loop,RefCnt),Calls_loop,Cs_loop,_,_)
	    ),Loops),
	split_multiple_loops(Loops,Loops_splitted),  
	(Loops_splitted=[]->
	    Inv_out=none,
	    add_forward_invariant(Entry_Call,([Non_loop|Chain],RefCnt), Inv_aux)
	    ;
		forward_invariant_once(inv(Entry_Call,Inv_aux),Loops_splitted,inv(Entry_call2,Inv_out)),
   		Entry_call2=Entry_Call,
   		(nad_is_bottom(Inv_out)->
        	assertz(unfeasible_chain_prefix(Entry_Call,RefCnt,[Non_loop|Chain])),
        	fail
        	;
        	add_forward_invariant(Entry_Call,([Non_loop|Chain],RefCnt), Inv_aux)
      	)
      ).

%an iterative phase
% start from the returned invariant of the suffix chain, 
% apply the loops once to obtain the return invariant
compute_forward_invariant([Phase|Chain],RefCnt,Entry_Call, Inv_out):-!,
    compute_forward_invariant(Chain,RefCnt,Entry_Call,Inv_0),
      findall((Head_loop,Calls_loop,Cs_loop),
	    (
	    member(Loop,Phase),
	    loop_ph(Head_loop,(Loop,RefCnt),Calls_loop,Cs_loop,_,_)
	    ),Loops),
	split_multiple_loops(Loops,Loops_splitted),    
    forward_invariant_fixpoint(inv(Entry_Call,Inv_0),Loops_splitted, inv(Entry_Call, Inv_aux)),
    forward_invariant_once(inv(Entry_Call,Inv_aux),Loops_splitted,inv(Entry_call2,Inv_out)),
%    include(nad_is_bottom,Cs_list,Bottoms),
%        length(Bottoms,N_bot),
%        length(Phase,N_phase),
%    ((Bottoms\=[],N_bot\=N_phase)-> format(user_error,'We could eliminate ~p loops in ~p~n',[N_bot,[Phase|Chain]]);true),
    Entry_call2=Entry_Call,
   (nad_is_bottom(Inv_out)->
        assertz(unfeasible_chain_prefix(Entry_Call,RefCnt,[Phase|Chain])),
        fail
     ;
        add_forward_invariant(Entry_Call,([Phase|Chain],RefCnt), Inv_aux)
     ).

% Apply the loops forwards or backwards once

backward_invariant_once(Initial_inv,Loops,inv(Head,Inv_out)):-
	apply_loops_backward(Loops,Initial_inv,Head,Cs_list),
	nad_list_lub(Cs_list,Inv_out).
	

apply_loops_backward([],_,_,[]).

apply_loops_backward([(Head_loop,Calls_loop,Cs_loop)|Loops],inv(Call_inv,Inv),Head,[Cs_final|Cs_list]):-
       foldl(get_call_inv,Calls_loop,(Call_inv,Inv,[]),(_,_,Total_inv)),
       nad_glb(Total_inv,Cs_loop,Cs_context),
       Head_loop=..[_|Vars],
       nad_project_group(Vars,Cs_context,Cs),
       copy_term((Head_loop,Cs),(Head,Cs_final)),
       apply_loops_backward(Loops,inv(Call_inv,Inv),Head,Cs_list).

get_call_inv(Call,(Head,Inv_0,Inv),(Head,Inv_0,Total_inv)):-
	copy_term((Head,Inv_0),(Call,Inv2)),
	nad_glb(Inv,Inv2,Total_inv).
	
forward_invariant_once(Initial_inv,Loops_splitted,inv(Head,Inv_out)):-
	apply_loops_forward(Loops_splitted,Initial_inv,Head,Cs_list),
	nad_list_lub(Cs_list,Inv_out).
	       
apply_loops_forward([],_,_,[]).

apply_loops_forward([(Head_loop,Call_loop,Cs_loop)|Loops],inv(Head_inv,Inv),Call,[Cs|Cs_list]):-
       copy_term(loop(Head_loop,Call_loop,Cs_loop),loop(Head_inv,Call,Cs_aux)),
       nad_glb(Inv,Cs_aux,Cs_context),
       Call=..[_|Vars],
       nad_project_group(Vars,Cs_context,Cs),
       apply_loops_forward(Loops,inv(Head_inv,Inv),Call,Cs_list).
       
      	   
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! compute_loops_transitive_closures(Entry:term,RefCnt:int) is det
% Complete transitive closure of each phase.
compute_loops_transitive_closures(Entry,RefCnt):-
	phase_loop(Phase,RefCnt,Entry,_,_),
	compute_phase_transitive_closure(Phase,RefCnt),
	compute_phase_transitive_star_closure(Phase,RefCnt),
	fail.
compute_loops_transitive_closures(_,_).

compute_phase_transitive_closure(Phase,RefCnt):-
	phase_loop(Phase,RefCnt,Head,Call,Inv_0),
    findall((Head_loop,Calls_loop,Cs_loop),
	    (
	    member(Loop,Phase),
	    loop_ph(Head_loop,(Loop,RefCnt),Calls_loop,Cs_loop,_,_)
	 ),Loops),
	 split_multiple_loops(Loops,Loops_splitted),    
     transitive_closure_invariant_fixpoint(inv(Head,Call,Inv_0),Loops_splitted,inv(Entry_out,Call_out, Trans_closure)),
     add_phase_transitive_closure(Phase,RefCnt,Entry_out,Call_out,Trans_closure).

compute_phase_transitive_star_closure(Phase,RefCnt):-
	phase_transitive_closure(Phase,RefCnt,Head,Call,Inv),
	Head=..[_|Vars_head],
	Call=..[_|Vars_Call],
	phase_loop(Phase,RefCnt,Head,Call,Inv_0),
	nad_project(Vars_head,Inv_0,Inv_0_head),
	maplist(zip_with_op2('='),Vars_head,Vars_Call,Equalities),
	append(Equalities,Inv_0_head,No_iterations_inv),
	nad_list_lub([No_iterations_inv,Inv],Inv_star),
	add_phase_transitive_star_closure(Phase,RefCnt,Head,Call,Inv_star).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Low level fixpoint computations



backward_invariant_fixpoint(inv(Head,Inv_0),Loops,inv(Head,Inv_out),inv(Head,Inv_star_out)):-
    low_level_backward_invariant_fixpoint(inv(Head,Inv_0),Loops,Inv_out,Inv_star_out).
    
forward_invariant_fixpoint(inv(Head,Inv_0),Loops,inv(Head,Inv_out)):-
	low_level_forward_invariant_fixpoint(inv(Head,Inv_0),Loops,Inv_out).

transitive_closure_invariant_fixpoint(inv(Entry,Head,Inv_0),Loops,inv(Entry,Head,Inv_out)):-
   low_level_transitive_closure_invariant_fixpoint(inv(Entry,Head,Inv_0),Loops,Inv_out).

    
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%transform the initial invariant and the loops into PPL polyhedra
%we use these polyhedra directly to avoid the overhead cost of translating back and forth

% For each loop we generate a tuple Loop_handle:(Extra_dim,Pre_maps,Post_map,Handle)
% * Extra_dim:int  number extra dimensions that the invariant has to have to be able to combine it with this loop	
% * Pre_maps:list(list(var-var)) list of maps (partial functions) that allow us to transform the invariant into the adequate dimensions
%            -we obtain a transformed invariant for each map and join them together with the loop to apply it
%            -Forward and transitive invariants have only one Pre_map
%            -All functions are total
% * Post_map:list(var-var) a map (partial function) used to transform and eliminate the invariants resulting from applying the loops
%             this function is usually partial
% * Handle:int identifier of the polyhedron object
   
low_level_backward_invariant_fixpoint(inv(Head_inv,Inv),Loops,Inv_plus_out,Inv_star_out):-
	to_numbervars_nu( (Head_inv,Inv) , _Vars, (_Head_ground,Inv_0_ground), Dim),
	to_ppl_dim(c, Dim, Inv_0_ground, Inv_0_handle), 
	
	maplist(get_back_loop_handle,Loops,Loop_handles),
	low_level_apply_loops(Loop_handles,Inv_0_handle,Inv_1_handle),
	%compute the backward invariant
	low_level_invariant_fixpoint(0,Inv_1_handle,Loop_handles,Inv_plus),
	%compute the upper bound of the invariant and the initial invariant
	ppl_Polyhedron_upper_bound_assign(Inv_0_handle,Inv_plus),
	maplist(delete_loop_handle,Loop_handles),
	% obtain the constrants of the resulting polyhedron
	Head_inv=..[_|Vars],
	length(Vars,Dim),
	from_ppl(c , Inv_0_handle, Dim, Vars, Inv_star_out), 
	from_ppl(c , Inv_plus, Dim, Vars, Inv_plus_out), 
	ppl_delete_Polyhedron(Inv_0_handle),
	ppl_delete_Polyhedron(Inv_plus).

low_level_forward_invariant_fixpoint(inv(Head_inv,Inv),Loops,Inv_out):-
	to_numbervars_nu( (Head_inv,Inv) , _Vars, (_Head_ground,Inv_0_ground), Dim),
	to_ppl_dim(c, Dim, Inv_0_ground, Inv_0_handle), 
	maplist(get_forward_loop_handle,Loops,Loop_handles),
	% call the fixpoint predicate
	low_level_invariant_fixpoint(0,Inv_0_handle,Loop_handles,Inv_final_handle),
	maplist(delete_loop_handle,Loop_handles),
	% obtain the constrants of the resulting polyhedron
	Head_inv=..[_F|Vars],
	from_ppl(c , Inv_final_handle,_, Vars, Inv_out), 
	ppl_delete_Polyhedron(Inv_final_handle).
		
low_level_transitive_closure_invariant_fixpoint(inv(Entry_inv,Head_inv,Inv),Loops,Inv_out):-
	Loops=[Loop1|_More_loops],
	copy_term(Loop1,(Head_inv,Call,_)),
	%Here we do it a little bit differently, the loops' polyhedron have 3 times the variables of the head 
	%Entry,Head and Call so we don't have to transform them every time
	%the first variables (Entry) have no information 
	to_numbervars_nu( (Entry_inv,Head_inv,Call,Inv) , _Vars, (Entry_ground,Head_ground,Call_ground,Inv_0_ground), _Dim),
	Entry_inv=..[F|Vars1],
	Head_inv=..[F|Vars2],
	append(Vars1,Vars2,Vars),
	length(Vars,Dim_inv),
	to_ppl_dim(c, Dim_inv, Inv_0_ground, Inv_0_handle), 
	maplist(get_transitive_loop_handle(Entry_ground,Head_ground,Call_ground),Loops,Loop_handles),
	% call the fixpoint predicate
	low_level_invariant_fixpoint(0,Inv_0_handle,Loop_handles,Inv_final_handle),
	maplist(delete_loop_handle,Loop_handles),
	% obtain the constrants of the resulting polyhedron

	from_ppl(c , Inv_final_handle, _, Vars, Inv_out), 
	ppl_delete_Polyhedron(Inv_final_handle).   



%! low_level_invariant_fixpoint(+Count:int,+Inv:ppl_polyhedron,+Loops:list(loop_handle),-Inv_out:ppl_polyhedron) is det
% This predicate implements a fixpoint computation that apply the loops Loops to Inv iteratively until a fixpoint is reached.
low_level_invariant_fixpoint(Count,Inv,Loops,Inv_out):-
	widening_frequency(Widening_freq),
	low_level_apply_loops(Loops,Inv,NewInv),
	ppl_new_C_Polyhedron_from_C_Polyhedron(Inv,Inv_lub),
	ppl_Polyhedron_upper_bound_assign(Inv_lub,NewInv),


	(ppl_Polyhedron_contains_Polyhedron(Inv, Inv_lub)->
	  ppl_delete_Polyhedron(Inv_lub),
	  ppl_delete_Polyhedron(NewInv),
	  Inv_out=Inv
	;
	 (Count>=Widening_freq ->
	   ppl_Polyhedron_H79_widening_assign(Inv_lub,Inv),
	   ppl_delete_Polyhedron(Inv),
	   ppl_delete_Polyhedron(NewInv),
	   Next_inv=Inv_lub,
	   Count1=0
	 ;
	  Next_inv=Inv_lub,
	  ppl_delete_Polyhedron(NewInv),
	  ppl_delete_Polyhedron(Inv),
	  Count1 is Count+1
	 ),
	 low_level_invariant_fixpoint(Count1,Next_inv,Loops,Inv_out)
	).
	

%! low_level_apply_loops(+Loops:list(loop_handle),+Inv:ppl_polyhedron,-Inv_aux:ppl_polyhedron) is det
% apply a set of loops Loops to the initial invariant Inv and compute the upper bound of their application
% at the end of the predicate only one new ppl_polyhedron is left with the resulting new invariant
low_level_apply_loops(Loops,Inv,Inv_out):-
	maplist(low_level_apply_loop(Inv),Loops,[New_inv|New_invs]),
	foldl(compress_and_delete,New_invs,New_inv,Inv_out).


low_level_apply_loop(Inv,(Extra_dim,Pre_map,Post_map,Loop_handle),Inv_out):-
	ppl_new_C_Polyhedron_from_C_Polyhedron(Inv,Inv_extended),
	ppl_Polyhedron_add_space_dimensions_and_embed(Inv_extended,Extra_dim),
	apply_pre_maps(Pre_map,Inv_extended,Mapped_inv),
	ppl_Polyhedron_intersection_assign(Mapped_inv,Loop_handle),
	apply_post_map(Mapped_inv,Post_map,Inv_out).

compress_and_delete(Inv2,Inv,Inv):-
	ppl_Polyhedron_upper_bound_assign(Inv,Inv2),
	ppl_delete_Polyhedron(Inv2).

apply_pre_maps([Map],Inv_extended,Inv_extended):-!,
	ppl_Polyhedron_map_space_dimensions(Inv_extended,Map).

apply_pre_maps([Map|Maps],Inv_extended,Mapped_inv):-
	ppl_new_C_Polyhedron_from_C_Polyhedron(Inv_extended,Inv_extended_cp),
	ppl_Polyhedron_map_space_dimensions(Inv_extended_cp,Map),
	apply_pre_maps(Maps,Inv_extended,Mapped_inv),
	ppl_Polyhedron_intersection_assign(Mapped_inv,Inv_extended_cp),
	ppl_delete_Polyhedron(Inv_extended_cp).
	
apply_post_map(Inv,Map,Inv):-
	ppl_Polyhedron_map_space_dimensions(Inv,Map).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
%these predicates take care of creating the loop_handle for the different kind of invariants
	
get_back_loop_handle((Head,Calls,Inv),(Extra_dim,Pre_maps,Post_map,Handle)):-
	Calls=[_|_],!,
	ground_copy((Head,Calls,Inv),(Head_gr,Calls_gr,Inv_gr)),
	Head_gr=..[_|Head_vars],
	term_variables(Calls,Call_vars),
	length(Head_vars,N),
	length(Call_vars,Extra_dim),
	foldl(make_complete_map_to_call(Head_gr,Calls_gr),Calls_gr,[],Pre_maps),
	identity_function(Head_vars,Post_map),
	Dim is N+Extra_dim,
	to_ppl_dim(c, Dim, Inv_gr, Handle).	
	
get_back_loop_handle((Head,Call,Inv),(Extra_dim,Pre_map,Post_map,Handle)):-
	ground_copy((Head,Call,Inv),(Head_gr,Call_gr,Inv_gr)),
	Head_gr=..[_|Head_vars],
	length(Head_vars,Extra_dim),
	make_complete_map_to_call(Head_gr,[Call_gr],Call_gr,[],Pre_map),
	identity_function(Head_vars,Post_map),
	Dim is Extra_dim*2,
	to_ppl_dim(c, Dim, Inv_gr, Handle).		
	
get_forward_loop_handle((Head,Call,Inv),(Extra_dim,[Pre_map],Post_map,Handle)):-
	ground_copy((Head,Call,Inv),(Head_gr,Call_gr,Inv_gr)),
	Head_gr=..[_|Head_vars],
	Call_gr=..[_|Call_vars],
	append(Head_vars,Call_vars,Total_vars),
	length(Head_vars,Extra_dim),
	identity_function(Total_vars,Pre_map),
	make_map_to_call(Call_gr,Head_gr,[],[Post_map]),
	Dim is Extra_dim*2,
	to_ppl_dim(c, Dim, Inv_gr, Handle).		
	
get_transitive_loop_handle(Entry_gr,Head_gr,Call_gr,(Head,Call,Inv),(Extra_dim,[Pre_map],Post_map,Handle)):-
	ground_copy((Head,Call,Inv),(Head_gr,Call_gr,Inv_gr)),
	Head_gr=..[_|Head_vars],
	length(Head_vars,Extra_dim),
	Entry_gr=..[_|Entry_vars],
	Call_gr=..[_|Call_vars],
	ut_flat_list([Entry_vars,Head_vars,Call_vars],All_vars),
	identity_function(All_vars,Pre_map),
	identity_function(Entry_vars,Post_map1),
	make_map_to_call(Call_gr,Head_gr,[],[Post_map2]),
	append(Post_map1,Post_map2,Post_map),
	Dim is Extra_dim*3,
	to_ppl_dim(c, Dim, Inv_gr, Handle).	

delete_loop_handle((_,_,_,Handle)):-
	ppl_delete_Polyhedron(Handle).
	
make_map_to_call(Term,Term2,Maps,[Map|Maps]):-
	Term=..[_|Vars],
	Term2=..[_|Vars2],
	maplist(zip_with_op2('-'),Vars,Vars2,Map).
make_complete_map_to_call(Head,Calls,Call,Maps,[Map|Maps]):-
	Head=..[_|Vars],
	Call=..[_|Vars2],
	maplist(zip_with_op2('-'),Vars,Vars2,Map1),
	maplist(zip_with_op2('-'),Vars2,Vars,Map2),
	append(Map1,Map2,Map3),
	foldl(make_complete_map_to_call_1(Call),Calls,Map3,Map).
make_complete_map_to_call_1(Call,Call,Map,Map):-!.
make_complete_map_to_call_1(_Call,Call2,Map,Map2):-
	Call2=..[_|Vars2],
	identity_function(Vars2,Map1),
	append(Map1,Map,Map2).

identity_function(Vars,Identity):-	
	maplist(zip_with_op2('-'),Vars,Vars,Identity).