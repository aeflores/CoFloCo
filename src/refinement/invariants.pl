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
		      forward_invariant/4,
		      scc_forward_invariant/3,
		      phase_transitive_closure/5,
		      add_scc_forward_invariant/3]).

:- use_module('../db',[loop_ph/6,phase_loop/5]).
:- use_module(chains,[chain/3]).


:- use_module('../utils/cofloco_utils',[assign_right_vars/3]).
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
:- use_module(stdlib(polyhedra_ppl),[to_ppl_dim/4,from_ppl/5]).

:-use_module(stdlib(polyhedra_ppl)).



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
%	format('~p~n',[backward_invariant(E,(Chain,RefCnt),Hash,EPat)]),
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
	%format('~p~n',forward_invariant(E,(Chain,RefCnt),Hash,IPat)),
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




%! partial_backward_invariant(Chain:chain,Head:term,Hash_forward_inv:(int,polyhedron),Inv:polyhedron)
% This is a cacheing mechanism to increase performance. many chains have a common 
% prefix and that can be used to avoid redundant computations.
%
% partial_backward_invariant stores the backward invariant of a fragment of chain Chain
% because the backward invariant might depend  on the forward invariants, it contains the 
% forward invariant that was used. 
% Any chain that has Chain as a prefix and has the same forward invariant Hash_forward_inv will have the same backward invariant
:-dynamic partial_backward_invariant/4.



%! compute_backward_invariants(+Head:term,+RefCnt:int) is det
% for each chain, try to compute the backward invariant.
% if it fails it is because it is not feasible and we can discard the chain
% otherwise we store the invariant
compute_backward_invariants(Head,RefCnt):-
    chain(Head,RefCnt,Chain),
    reverse(Chain,RevChain),
    (compute_backward_invariant(RevChain,[],Head,RefCnt,Entry_pattern)->
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
	forward_invariant(Head,([Ph|Prev_chain],RefCnt),Hash_local_inv,Local_inv),
    partial_backward_invariant([Ph|Chain],Head,(Hash_local_inv,Local_inv2),Entry_pattern),
    Local_inv==Local_inv2,!,
    counter_increase(compressed_invs,1,_),
    Entry_pattern\==[0=1].

% the base case of the chain, the backward invariant is the cost equation definition
% and the corresponding forward invariant
compute_backward_invariant([Base_case],Prev_chain,Head,RefCnt,Entry_pattern_normalized):-!,
    loop_ph(Head,(Base_case,RefCnt),none,Cs_1,_,_),
    forward_invariant(Head,([Base_case|Prev_chain],RefCnt),_Hash,Inv),
   % append(Cs_1,Inv,Cs),
    nad_glb(Cs_1,Inv,Entry_pattern),
	\+nad_is_bottom(Entry_pattern),
	nad_normalize_polyhedron(Entry_pattern,Entry_pattern_normalized).
 
 % We have a phase that is not iterative (Ph is a number).
 % The backward invariant is obtained by applying the loop definition once to the
 % backward invariant of the rest of the chain
compute_backward_invariant([Ph|Chain],Prev_chain,Head,RefCnt,Entry_pattern_normalized):-
	number(Ph),!,
	copy_term(Head,Call),
	compute_backward_invariant(Chain,[Ph|Prev_chain],Call,RefCnt,Initial_inv),
	loop_ph(Head,(Ph,RefCnt),Call,Cs,_,_),
	forward_invariant(Head,([Ph|Prev_chain],RefCnt),Hash_local_inv,Local_inv),
	Head=..[_|EVars],
	%ut_flat_list([Local_inv,Cs,Initial_inv],Cs_2),
	nad_list_glb([Local_inv,Cs,Initial_inv],Cs_2),
	nad_project_group(EVars,Cs_2,Entry_pattern),
	%even if the invariant is unfeasible, we store to save time when computing invariants with the same suffix
	nad_normalize_polyhedron(Entry_pattern,Entry_pattern_normalized),
	(nad_is_bottom(Entry_pattern_normalized)->
	  assert(partial_backward_invariant([Ph|Chain],Head,(Hash_local_inv,Local_inv),[0=1])),
	  fail
	;
	  assert(partial_backward_invariant([Ph|Chain],Head,(Hash_local_inv,Local_inv),Entry_pattern_normalized))
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
	    loop_ph(Head_loop,(Loop,RefCnt),Call_loop,Cs_loop,_,_),
	    nad_glb(Local_inv,Cs_loop,Cs_1)
	    ),Loops),
	
	backward_invariant_fixpoint(inv(Head,Initial_inv),Loops,inv(Head_out,It_pattern)),
	Head=..[_|EVars],
	Head=Head_out,
	nad_project_group(EVars,Cs,Extra_conds),
	nad_glb(Extra_conds,It_pattern,Entry_pattern),
	Head=Head_loop,
	nad_normalize_polyhedron(Entry_pattern,Entry_pattern_normalized),
	(nad_is_bottom(Entry_pattern_normalized)->
	assert(partial_backward_invariant([Ph|Chain],Head,(Hash_local_inv,Local_inv),[0=1])),
	fail
	;
	assert(partial_backward_invariant([Ph|Chain],Head,(Hash_local_inv,Local_inv),Entry_pattern_normalized))
	).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	

%! unfeasible_chain_suffix(Head:term,RefCnt:int,Chain_suffix:chain)
% store suffixes of chains that are not feasible in order to avoid repeating computation of invariants
% that are going to fail.
:-dynamic unfeasible_chain_suffix/3.

%! compute_forward_invariants(Entry_Call:term,RefCnt:int) is det
% for each chain, if none of the suffixes is clearly unfeasible (because we computed it before)
% we try to compute the forward invariant.
% if we fail to compute it, then we remove the chain.
% if we don't fail, we do nothing and the chain is not removed.
compute_forward_invariants(Entry_Call,RefCnt):-

	chain(Entry_Call,RefCnt,Chain),
	(has_infeasible_suffix(Entry_Call,RefCnt,Chain)->
	   retract(chains:chain(Entry_Call,RefCnt,Chain))
	;
	\+compute_forward_invariant(Chain,RefCnt,Entry_Call,_),
	  retract(chains:chain(Entry_Call,RefCnt,Chain))
	  ),   
	fail.
compute_forward_invariants(_,_).


has_infeasible_suffix(Entry_Call,RefCnt,Chain):-
	unfeasible_chain_suffix(Entry_Call,RefCnt,Chain_suffix),
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
compute_forward_invariant([Entry_phase],RefCnt,Head, Inv_out):-
    number(Entry_phase),
    loop_ph(Head,(Entry_phase,RefCnt),Call,Cs,_,_),Call\==none,  !,
    Call=..[_|Vars2],
    scc_forward_invariant(Head,_,Inv),
    nad_glb(Inv,Cs,Cs_1),
    nad_project_group(Vars2,Cs_1,Inv_out),
    Head=Call,
    (nad_is_bottom(Inv_out)->
        assert(unfeasible_chain_suffix(Head,RefCnt,[Entry_phase])),
        fail
     ;
        add_forward_invariant(Head,([Entry_phase],RefCnt), Inv)
     ).


% a chain with only a base case
% we start from the precondition (scc_forward_invariant) and store that invariant
compute_forward_invariant([Entry_phase],RefCnt,Entry_Call,none):-
    number(Entry_phase),!,%a non recursive phase
    scc_forward_invariant(Entry_Call,_,Inv),
    add_forward_invariant(Entry_Call,([Entry_phase],RefCnt),Inv).


%initial phase that is recursive
% start from the precondition (scc_forward_invariant) and apply the loops until
% reaching a fixpoint
compute_forward_invariant([Entry_phase],RefCnt,Entry_Call, Inv_out):-!,
    scc_forward_invariant(Entry_Call,_,Inv_0),
    findall((Head_loop,Call_loop,Cs_loop),
	    (
	    member(Loop,Entry_phase),
	    loop_ph(Head_loop,(Loop,RefCnt),Call_loop,Cs_loop,_,_)
	    ),Loops),
    forward_invariant_fixpoint(inv(Entry_Call,Inv_0),Loops,inv(Entry_Call,Inv_aux)),
        apply_loops_external(Loops,inv(Entry_Call,Inv_aux),Entry_call2,Cs_list),
    nad_list_lub(Cs_list,Inv_out),
    Entry_call2=Entry_Call,
   (nad_is_bottom(Inv_out)->
        assert(unfeasible_chain_suffix(Entry_Call,RefCnt,[Entry_phase])),
        fail
     ;
        add_forward_invariant(Entry_Call,([Entry_phase],RefCnt), Inv_aux)
    ).

%an intermediate non-iterative phase
% start from the returned invariant of the suffix chain, store that invariant
% and apply the loops once to obtain the return invariant
compute_forward_invariant([Non_loop|Chain],RefCnt,Entry_Call,Inv_out):-
    number(Non_loop),
    loop_ph(Entry_Call,(Non_loop,RefCnt),Call,Cs,_,_),Call\==none,!,
    compute_forward_invariant(Chain,RefCnt,Entry_Call,Inv_aux), 
    Call=..[_|Vars],
    nad_glb(Inv_aux,Cs,Cs_1),
    nad_project_group(Vars,Cs_1,Inv_out),
    Call=Entry_Call,
   (nad_is_bottom(Inv_out)->
        assert(unfeasible_chain_suffix(Entry_Call,RefCnt,[Non_loop|Chain])),
        fail
        ;
        add_forward_invariant(Entry_Call,([Non_loop|Chain],RefCnt), Inv_aux)
      ).

%The base case in a chain with multiple phases
% take from the returned invariant of the suffix chain and store it
compute_forward_invariant([Phase|Chain],RefCnt,Entry_Call, Inv_out):-
    number(Phase),!,
    compute_forward_invariant(Chain,RefCnt,Entry_Call, Inv_out),
    add_forward_invariant(Entry_Call,([Phase|Chain],RefCnt), Inv_out).

%an intermediate iterative phase
% start from the returned invariant of the suffix chain, 
% apply the loops once to obtain the return invariant
compute_forward_invariant([Phase|Chain],RefCnt,Entry_Call, Inv_out):-!,
    compute_forward_invariant(Chain,RefCnt,Entry_Call,Inv_0),
      findall((Head_loop,Call_loop,Cs_loop),
	    (
	    member(Loop,Phase),
	    loop_ph(Head_loop,(Loop,RefCnt),Call_loop,Cs_loop,_,_)
	    ),Loops),
    forward_invariant_fixpoint(inv(Entry_Call,Inv_0),Loops, inv(Entry_Call, Inv_aux)),
    apply_loops_external(Loops,inv(Entry_Call,Inv_aux),Entry_call2,Cs_list),
    nad_list_lub(Cs_list,Inv_out),
    Entry_call2=Entry_Call,
   (nad_is_bottom(Inv_out)->
        assert(unfeasible_chain_suffix(Entry_Call,RefCnt,[Phase|Chain])),
        fail
     ;
        add_forward_invariant(Entry_Call,([Phase|Chain],RefCnt), Inv_aux)
     ).

apply_loops_external([],_,_,[]).
apply_loops_external([(Head_loop,Call_loop,Cs_loop)|Loops],inv(Head_inv,Inv),Call,[Cs|Cs_list]):-
       copy_term(loop(Head_loop,Call_loop,Cs_loop),loop(Head_inv,Call,Cs_aux)),
       nad_glb(Inv,Cs_aux,Cs_context),
       Call=..[_|Vars],
       nad_project_group(Vars,Cs_context,Cs),
       apply_loops_external(Loops,inv(Head_inv,Inv),Call,Cs_list).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! compute_loops_transitive_closures(Entry:term,RefCnt:int) is det
% Complete transitive closure of each phase.
compute_loops_transitive_closures(Entry,RefCnt):-
	phase_loop(Phase,RefCnt,Entry,_,_),
	compute_phase_transitive_closure(Phase,RefCnt),
	fail.
compute_loops_transitive_closures(_,_).

compute_phase_transitive_closure(Phase,RefCnt):-
	phase_loop(Phase,RefCnt,Head,Call,Inv_0),
        findall((Head_loop,Call_loop,Cs_loop),
	    (
	    member(Loop,Phase),
	    loop_ph(Head_loop,(Loop,RefCnt),Call_loop,Cs_loop,_,_)
	    ),Loops),
        transitive_closure_invariant_fixpoint(inv(Head,Call,Inv_0),Loops,inv(Entry_out,Call_out, Trans_closure)),
        add_phase_transitive_closure(Phase,RefCnt,Entry_out,Call_out,Trans_closure).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Low level fixpoint computations
% split the invariants and the loops into independent components to compute a fixpoint for
% each component independently


backward_invariant_fixpoint(inv(Head,Inv_0),Loops,inv(Head,Inv_out)):-
 %   partition_invariant_and_loops(inv(Head,Inv_0),Loops,Groups_inv_loops),
 %   maplist(low_level_backward_invariant_fixpoint,Groups_inv_loops,Invs),
 %   ut_flat_list(Invs,Inv_out).
    low_level_backward_invariant_fixpoint((inv(Head,Inv_0),Loops),Inv_out).
    
forward_invariant_fixpoint(inv(Head,Inv_0),Loops,inv(Head,Inv_out)):-
%	partition_invariant_and_loops(inv(Head,Inv_0),Loops,Groups_inv_loops),
 %  maplist(low_level_forward_invariant_fixpoint,Groups_inv_loops,Invs),
 %   ut_flat_list(Invs,Inv_out).  
	low_level_forward_invariant_fixpoint((inv(Head,Inv_0),Loops),Inv_out).

transitive_closure_invariant_fixpoint(inv(Entry,Head,Inv_0),Loops,inv(Entry,Head,Inv_out)):-
 %   partition_invariant_and_loops(inv(Entry,Head,Inv_0),Loops,Groups_inv_loops),
%    maplist(low_level_transitive_closure_invariant_fixpoint,Groups_inv_loops,Invs),
%    ut_flat_list(Invs,Inv_out).
   low_level_transitive_closure_invariant_fixpoint((inv(Entry,Head,Inv_0),Loops),Inv_out).

% auxiliar procedures to split a set of loops into their independent components


% get all the constraints of the invariant and all the loops and  unify them to a single set of variables
% if we have variables that are independent with respect to all constraints of all loops, they will never interact in the invariant computation
% and we can split the invariant computation into parts

partition_invariant_and_loops(inv(Head,Inv_0),Loops,Groups_inv_loops):-
	copy_term((inv(Head,Inv_0),Loops),(inv(Head_out,Inv_aux),Loops1)),
	get_extra_connection_constraint(Inv_aux,Vars_constr),
	foldl(accumulate_loop_constr,Loops1,(Head_out,[Vars_constr|Inv_aux]),(_,All_constraints)),
	Head_out=..[_|Vars],
    group_relevant_vars(Vars,All_constraints,Groups,_),  
    maplist(get_inv_and_loop_part(Head_out,inv(Head,Inv_0),Loops),Groups,Groups_inv_loops).
    
partition_invariant_and_loops(inv(Entry,Head,Inv_0),Loops,Groups_inv_loops):-
	copy_term((inv(Entry,Head,Inv_0),Loops),(inv(Entry_out,Entry_out,Inv_aux),Loops1)),
	foldl(accumulate_loop_constr,Loops1,(Entry_out,Inv_aux),(_,All_constraints)),
	Entry_out=..[_|Vars],
    group_relevant_vars(Vars,All_constraints,Groups,_),
    maplist(get_inv_and_loop_part(Entry_out,inv(Entry,Head,Inv_0),Loops),Groups,Groups_inv_loops).  
 
% heuristic to connect extra variables that might be related through a constant value
% for example x>=0 y<0 implies that y<X which might be important
% the typical example is x=0, y=0 and in each loop x=x+1 and y=y+1. We want to know that after any number of loops x=y
get_extra_connection_constraint(Inv_aux,Vars):-
	include(only_one_var,Inv_aux,Related_to_constants),
	term_variables(Related_to_constants,Vars). 
only_one_var(X):-
	term_variables(X,[_]).	
    
accumulate_loop_constr((Head,Head,Cs),(Head,Css),(Head,Csss)):-
	append(Cs,Css,Csss).


get_inv_and_loop_part(Head_aux,inv(Head_inv,Inv),Loops,(Sel_vars,_),(inv(Head_part,Inv_part),Loops_parts_reduced)):-
	Head_inv=..[F|Vars_total],
	copy_term((Head_aux,Sel_vars),(Head_inv,Sel_vars1)),
	slice_relevant_constraints_and_vars(Sel_vars1,Vars_total,Inv,_,Inv_part),
	Head_part=..[F|Sel_vars1],
	get_loops_parts(Head_aux,Sel_vars,Loops,Loops_parts_reduced).
	
get_inv_and_loop_part(Head_aux,inv(Head_inv,Call_inv,Inv),Loops,(Sel_vars,_),(inv(Head_part,Call_part,Inv_part),Loops_parts_reduced)):-
	Head_inv=..[F|_],
	copy_term((Head_aux,Sel_vars),(Head_inv,Sel_vars1)),
	copy_term((Head_aux,Sel_vars),(Call_inv,Sel_vars2)),
	append(Sel_vars1,Sel_vars2,Sel_vars_total),
	term_variables((Head_inv,Call_inv),Vars_total),
	slice_relevant_constraints_and_vars(Sel_vars_total,Vars_total,Inv,_,Inv_part),
	Head_part=..[F|Sel_vars1],
	Call_part=..[F|Sel_vars2],
	get_loops_parts(Head_aux,Sel_vars,Loops,Loops_parts_reduced).
		
get_loops_parts(Head_aux,Sel_vars,Loops,Loops_parts_reduced):-
	maplist(get_loop_part(Head_aux,Sel_vars),Loops,[Loop1|Loops_parts]),
	foldl(unify_loop_variables,Loops_parts,Loop1,_),
	from_list_sl([Loop1|Loops_parts],Loops_parts_reduced).
	
get_loop_part(Head_aux,Sel_vars,(Head_loop,Call_loop,Cs_loop),(Head_part,Call_part,Cs_part_sorted)):-
	copy_term((Head_aux,Sel_vars),(Head_loop,Sel_vars1)),
	copy_term((Head_aux,Sel_vars),(Call_loop,Sel_vars2)),
	append(Sel_vars1,Sel_vars2,Sel_vars_total),
	Head_loop=..[F|Vars_total1],Call_loop=..[F|Vars_total2],
	append(Vars_total1,Vars_total2,Vars_total),
	slice_relevant_constraints_and_vars(Sel_vars_total,Vars_total,Cs_loop,_,Cs_part),
	from_list_sl(Cs_part,Cs_part_sorted),
	Head_part=..[F|Sel_vars1],
	Call_part=..[F|Sel_vars2].

unify_loop_variables((Head,Call,_Inv),(Head,Call,Inv1),(Head,Call,Inv1)).   
    
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%transform the initial invariant and the loops into PPL polyhedra
%we use these polyhedra directly to avoid the overhead cost of translating back and forth

low_level_backward_invariant_fixpoint((inv(Head_inv,Inv),Loops),Inv_out):-
	Loops=[Loop1|_More_loops],
	%create the ppl_polyhedra from the constraints
	%the way the polyhedra are created and their variables named is what determines how the invariant is computed
	copy_term(Loop1,(Head_new,Head_inv,_)),	
	to_numbervars_nu( (Head_inv,Head_new,Inv) , _Vars, (Call_ground,Head_ground,Inv_0_ground), Dim),
	to_ppl_dim(c, Dim, Inv_0_ground, Inv_0_handle), 
	maplist(get_loop_handle(Head_ground,Call_ground,Dim),Loops,Loops_handles),
	Call_ground=..[F|Var_calls],
	% call the fixpoint predicate
	low_level_backward_invariant_fixpoint_1(Inv_0_handle,Var_calls,Loops_handles,Inv_final_handle),
	% obtain the constrants of the resulting polyhedron
	Dim2 is Dim//2,
	length(Vars,Dim2),
	from_ppl(c , Inv_final_handle, Dim2, Vars, Inv_out), 
	Head_inv=..[F|Vars],
	ppl_delete_Polyhedron(Inv_final_handle).

	
low_level_transitive_closure_invariant_fixpoint((inv(Entry_inv,Head_inv,Inv),Loops),Inv_out):-
	Loops=[Loop1|_More_loops],
	copy_term(Loop1,(Head_inv,Call,_)),
	%create the ppl_polyhedra from the constraints
	%the way the polyhedra are created and their variables named is what determines how the invariant is computed
	to_numbervars_nu( (Entry_inv,Head_inv,Call,Inv) , _Vars, (_Entry_ground,Head_ground,Call_ground,Inv_0_ground), Dim),
	to_ppl_dim(c, Dim, Inv_0_ground, Inv_0_handle), 
	maplist(get_loop_handle(Head_ground,Call_ground,Dim),Loops,Loops_handles),
	Head_ground=..[F|Var_head],
	% call the fixpoint predicate
	low_level_invariant_fixpoint(0,Var_head,Inv_0_handle,Loops_handles,Inv_final_handle),
	% obtain the constrants of the resulting polyhedron
	Dim2 is Dim//3,
	length(Vars1,Dim2),
	length(Vars2,Dim2),
	append(Vars1,Vars2,Vars),
	Dim3 is Dim2*2,
	from_ppl(c , Inv_final_handle, Dim3, Vars, Inv_out), 
	Entry_inv=..[F|Vars1],
	Head_inv=..[F|Vars2],
	ppl_delete_Polyhedron(Inv_final_handle).   

low_level_forward_invariant_fixpoint((inv(Head_inv,Inv),Loops),Inv_out):-
	Loops=[Loop1|_More_loops],
	copy_term(Loop1,(Head_inv,Head_new,_)),	
	%create the ppl_polyhedra from the constraints
	%the way the polyhedra are created and their variables named is what determines how the invariant is computed
	to_numbervars_nu( (Head_inv,Head_new,Inv) , _Vars, (Head_ground,Call_ground,Inv_0_ground), Dim),
	to_ppl_dim(c, Dim, Inv_0_ground, Inv_0_handle), 
	maplist(get_loop_handle(Head_ground,Call_ground,Dim),Loops,Loops_handles),
	Head_ground=..[F|Var_head],
	% call the fixpoint predicate
	low_level_invariant_fixpoint(0,Var_head,Inv_0_handle,Loops_handles,Inv_final_handle),
	% obtain the constrants of the resulting polyhedron
	Dim2 is Dim//2,
	length(Vars,Dim2),
	from_ppl(c , Inv_final_handle, Dim2, Vars, Inv_out), 
	Head_inv=..[F|Vars],
	ppl_delete_Polyhedron(Inv_final_handle).


get_loop_handle(Head_ground,Call_ground,Dim,(Head_loop,Call_loop,Cs_loop),Loop_handle):-
	copy_term((Head_loop,Call_loop,Cs_loop),(Head_ground,Call_ground,Cs_loop_ground)),
	to_ppl_dim(c, Dim, Cs_loop_ground, Loop_handle).


%first mandatory iteration
% given the initial invariant Inv we apply each of the loops and 
% obtain the convex hull of the results.
% the we call the normal fixpoint	
low_level_backward_invariant_fixpoint_1(Inv,Call_ground,Loops,Inv_out):-!,
	low_level_apply_loops(Loops,Call_ground,Inv,NewInv),
	ppl_delete_Polyhedron(Inv),
	length(Call_ground,N),
	ppl_Polyhedron_add_space_dimensions_and_embed(NewInv,N),
	low_level_invariant_fixpoint(0,Call_ground,NewInv,Loops,Inv_out).

%! low_level_invariant_fixpoint(+Count:int,+Var_head:list(number_var),+Inv:ppl_polyhedron,+Loops:list(ppl_polyhedron),-Inv_out:ppl_polyhedron) is det
% This predicate implements a fixpoint computation that apply the loops Loops to Inv iteratively until a fixpoint is reached.
low_level_invariant_fixpoint(Count,Var_head,Inv,Loops,Inv_out):-
	widening_frequency(Widening_freq),
	low_level_apply_loops(Loops,Var_head,Inv,NewInv),
	length(Var_head,N),
	ppl_Polyhedron_add_space_dimensions_and_embed(NewInv,N),
	
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
	 low_level_invariant_fixpoint(Count1,Var_head,Next_inv,Loops,Inv_out)
	).
	

%! low_level_apply_loops(+Loops:list(ppl_polyhedron),+Vars:list(number_var),+Inv:ppl_polyhedron,-Inv_aux:ppl_polyhedron) is det
% apply a set of loops Loops to the initial invariant Inv and compute the upper bound of their application
% depending on Vars and how the loops have been created, the are applied forwards, backwards or composing them.
% at the end of the predicate only one new ppl_polyhedron is left with the resulting new invariant
low_level_apply_loops([Loop],Vars,Inv,Inv_aux):-!,
	ppl_new_C_Polyhedron_from_C_Polyhedron(Loop,Inv_aux),	
	ppl_Polyhedron_intersection_assign(Inv_aux,Inv),
	ppl_Polyhedron_remove_space_dimensions(Inv_aux,Vars).
	
low_level_apply_loops([Loop|Loops],Vars,Inv,Inv_aux):-
	low_level_apply_loops(Loops,Vars,Inv,Inv_aux),
	ppl_new_C_Polyhedron_from_C_Polyhedron(Loop,Inv_aux2),
	ppl_Polyhedron_intersection_assign(Inv_aux2,Inv),
	ppl_Polyhedron_remove_space_dimensions(Inv_aux2,Vars),
	ppl_Polyhedron_upper_bound_assign(Inv_aux,Inv_aux2),
	ppl_delete_Polyhedron(Inv_aux2).	
