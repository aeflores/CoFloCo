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
  * relation2entry_invariant/3: This invariant maintains the relation between the variables at the beginning
    of a chain and the variables at some point of the chain. it is used to maximize the internal elements of 
    a cost structure.
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
		      relation2entry_invariant/3,
		      get_phase_star/4,
		      phase_transitive_closure/5,
		      add_scc_forward_invariant/3]).

:- use_module('../db',[loop_ph/6,phase_loop/5]).
:- use_module(chains,[chain/3]).


:- use_module('../utils/cofloco_utils',[assign_right_vars/3,add_equality_constraints/4,
normalize_constraint/2]).
:- use_module('../utils/polyhedra_optimizations',[nad_project_group/3,
					nad_consistent_constraints_group_aux/1,
					nad_is_bottom/1,
					group_relevant_vars/4,
					nad_normalize_polyhedron/2]).
:- use_module('../utils/polyhedra_optimizations',[]).	
:- use_module(stdlib(set_list)).
:- use_module(stdlib(counters),[counter_increase/3]).
:- use_module(stdlib(numeric_abstract_domains),[
	nad_glb/3,nad_list_glb/2,nad_project/3, nad_entails/3, nad_lub/6,nad_list_lub/2, nad_widen/5,
	nad_normalize/2,
	nad_false/1,nad_consistent_constraints/1]).
:- use_module(stdlib(utils),[ut_append/3,ut_flat_list/2, ut_member/2, ut_list_to_dlist/2,ut_split_at_pos/4]).
:- use_module(stdlib(profiling),[profiling_start_timer/1,profiling_stop_timer_acum/2]).
 
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
  
%! relation2entry_invariant(Head,Chain_RefCnt:(chain,int),InvT:inv(term,term,polyhedron))
%  This invariant maintains the relation between the variables at the beginning
%  of a chain and the variables at some point of the last phase (first in the list).
%  The last phase has been applied 0 or more times.
%  There is an invariant for each suffix of each chain.
%
% InvT=inv(Head_inv,Call_inv,Inv) where Inv is expressed in terms of the variables of Head_inv and Call_inv
:- dynamic relation2entry_invariant/3.

%! relation2entry_invariant_aux(Head,Chain_RefCnt:(chain,int),InvT:inv(term,term,polyhedron))
%  This invariant maintains the relation between the variables at the beginning
%  of a chain and the variables at some point of the last phase (first in the list).
%  The last phase has been applied 1 or more times.
%  This invariant is only an intermediate value to compute the relation2entry_invariant/3 of longer chains.
%  There is an invariant for each suffix of each chain.
%
% InvT=inv(Head_inv,Call_inv,Inv) where Inv is expressed in terms of the variables of Head_inv and Call_inv
:- dynamic relation2entry_invariant_aux/3.
  
 

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
	retractall(relation2entry_invariant(_,_,_)),
	retractall(relation2entry_invariant_aux(_,_,_)),
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
%	format('~p~n',forward_invariant(E,(Chain,RefCnt),Hash,IPat)),
	assertz(forward_invariant(Head,(Chain,RefCnt),Hash,Inv_normalized)).

%! add_scc_forward_invariant(+Phase:phase,+RefCnt:int,+Inv:polyhedron)
%  store the invariant if it does not already exits
add_scc_forward_invariant(Head,RefCnt,_) :-
	scc_forward_invariant(Head,RefCnt,_),!.
add_scc_forward_invariant(Head,RefCnt,Inv) :-
	nad_normalize_polyhedron(Inv,Inv_normalized),
	assertz(scc_forward_invariant(Head,RefCnt,Inv_normalized)).
	
%! add_relation2entry_invariant(+Phase:phase,+Chain_RefCnt:(chain,int),+Inv:polyhedron)
%  store the invariant if it does not already exits
add_relation2entry_invariant(Head,(Chain,RefCnt),_) :-
	relation2entry_invariant(Head,(Chain,RefCnt),_),!.
add_relation2entry_invariant(Head,(Chain,RefCnt),Inv) :-
	assertz(relation2entry_invariant(Head,(Chain,RefCnt),Inv)).
	
%! add_relation2entry_invariant_aux(+Phase:phase,+Chain_RefCnt:(chain,int),+Inv:polyhedron)
%  store the invariant if it does not already exits
add_relation2entry_invariant_aux(Head,(Chain,RefCnt),_) :-
	relation2entry_invariant_aux(Head,(Chain,RefCnt),_),!.
add_relation2entry_invariant_aux(Head,(Chain,RefCnt),Inv) :-
	assertz(relation2entry_invariant_aux(Head,(Chain,RefCnt),Inv)).	
	
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
	compute_relation2entry_invariants(Head,RefCnt),
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
    retract(chain(Head,RefCnt,Chain))
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
	
	backward_invariant_fixpoint_1(inv(Head,Initial_inv),Loops,inv(Head_out,It_pattern)),
%Fixme add external invariant to the fixpoint computation
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

%first mandatory iteration
% given the initial invariant inv(Head_inv,Inv) we apply each of the loops and 
% obtain the convex hull of the results.
% the we call the normal fixpoint
backward_invariant_fixpoint_1(inv(Head_inv,Inv),Loops,inv(Head_out,Inv_out)):-!,
	apply_loops_entry_pattern(Loops,inv(Head_inv,Inv),Head_new,Cs_list),
	nad_list_lub(Cs_list,NewInv),
%	nad_lubs_group(Cs_list,NewInv),
	backward_invariant_fixpoint(0,inv(Head_new,NewInv),Loops,inv(Head_out,Inv_out)).

	


%subsequent optional iterations
% given the initial invariant inv(Head_inv,Inv) we apply each of the loops and 
% obtain the convex hull of the results.
% then we check if we have reached a fixpoint.
% if not, we increase the widening counter or perform widening and start again
backward_invariant_fixpoint(Count,inv(Head_inv,Inv),Loops,inv(Head_out,Inv_out)):-
	widening_frequency(Widening_freq),
	apply_loops_entry_pattern(Loops,inv(Head_inv,Inv),Head_aux,Cs_list),
	nad_list_lub(Cs_list,Inv_1),
%	nad_lubs_group(Cs_list,Inv_1),
	Head_inv=..[_|Vars],

	Head_inv=Head_aux,
	
	nad_lub(Vars, Inv, Vars, Inv_1, Vars, JoinInv),
	(nad_entails(Vars, JoinInv, Inv)->
	   inv(Head_out,Inv_out)=inv(Head_aux,JoinInv)
	;
	 (Count>=Widening_freq ->
	   nad_widen(Vars,Inv,JoinInv,Vars,NewInv),
	   Count1=0
	 ;
	  NewInv=JoinInv,
	  Count1 is Count+1
	 ),
	 backward_invariant_fixpoint(Count1,inv(Head_aux,NewInv),Loops,inv(Head_out,Inv_out))
	).

% apply a set of loops inversely. This is like executing the loops backwards
% the invariant is combined with the loop definition such that the variables of the Call_loop coincide with
% the ones of the invariant Head_inv.
% then the combined polyhedron is projected onto the variables of the head of the loop Head_new
apply_loops_entry_pattern([],_,_,[]).
apply_loops_entry_pattern([(Head_loop,Call_loop,Cs_loop)|Loops],inv(Head_inv,Inv),Head_new,[Cs|Cs_list]):-
	copy_term(loop(Head_loop,Call_loop,Cs_loop),loop(Head_new,Head_inv,Cs_aux)),
	nad_glb(Inv,Cs_aux,Cs_context),
	Head_new=..[_|Vars],
	nad_project_group(Vars,Cs_context,Cs),
	apply_loops_entry_pattern(Loops,inv(Head_inv,Inv),Head_new,Cs_list).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


compute_relation2entry_invariants(Head,RefCnt):-
	chain(Head,RefCnt,Chain),
	compute_relation2entry_invariant(Chain,RefCnt,Head,_Inv),
	fail.
compute_relation2entry_invariants(_,_).

%! compute_relation2entry_invariant(+Chain:chain,+RefCnt:int,?Entry_Call:term,-Inv:inv(term,term,polyhedron)) is det
% given a chain fragment [P1,P2...PN], computes a invariant that relates the variables at the beginning
% of PN with the variables at any point during P1.
% This invariant is stored, but the invariant returned is a different one.
% The returned invariant is valid at any point after at least ONE iteration of P1 has been performed.
compute_relation2entry_invariant(Chain,RefCnt,Entry_Call,inv(Entry_Call_out,Call,Inv_out)):-
% if the invariant is already computed, we apply the loops of the phase once and return the result.
	relation2entry_invariant_aux(Entry_Call,(Chain,RefCnt),inv(Entry_Call_out,Call,Inv_out)),!.
  
  
% in the initial phase, if it's a non-iterative phase (number(Entry_phase)) the stored invariant
% is just a set of equalities
% the returned invariant is obtained by applying the loop once.
compute_relation2entry_invariant([Entry_phase],RefCnt,Head,inv(Head,Call, Inv_aux)):-
    number(Entry_phase),
    loop_ph(Head,(Entry_phase,RefCnt),Call,Inv_aux,_,_),Call\==none,
    !,
    Head=..[_|Vars_head],
    Call=..[_|Vars_call],
    add_equality_constraints(Vars_head, Vars_call, [], Inv),    
	%we save the invariant at the entry but we return the next one
    add_relation2entry_invariant(Entry_Call,([Entry_phase],RefCnt),inv(Head,Call, Inv)),
    add_relation2entry_invariant_aux(Entry_Call,([Entry_phase],RefCnt),inv(Head,Call, Inv_aux)).

%this is the case where the initial phase is also the final one.
% that is, this is a chain with only a base case
%the result of this call is never be used
compute_relation2entry_invariant([Entry_phase],RefCnt,Entry_Call,none):-
    number(Entry_phase),!,%a non recursive phase
    copy_term(Entry_Call,Head),
    Entry_Call=..[_|Vars_entry],
    Head=..[_|Vars_head],
    add_equality_constraints(Vars_entry, Vars_head, [], Inv),
    add_relation2entry_invariant(Entry_Call,([Entry_phase],RefCnt),inv(Entry_Call,Head,Inv)).

% an initial phase that is recursive. we return the transitive closure
% and we store the transitive reflexive closure
% we store that invariant and apply the loops once more to obtain the return invariant
compute_relation2entry_invariant([Entry_phase],RefCnt,Entry_Call,inv(Head,Call, Inv_aux)):-!,
    copy_term(Entry_Call,Head),

    phase_transitive_closure(Entry_phase,RefCnt,Head,Call,Inv_aux),
    get_phase_star(Head,Call,Entry_phase,Inv),
  
    add_relation2entry_invariant(Head,([Entry_phase],RefCnt),inv(Head,Call, Inv)),
    add_relation2entry_invariant_aux(Head,([Entry_phase],RefCnt),inv(Head,Call, Inv_aux)).
	    

% not the last phase and non-recursive but not the leaf
% we start with the invariant of the suffix
% we store that invariant and apply the loop once to obtain the return invariant
compute_relation2entry_invariant([Non_loop|Chain],RefCnt,Entry_Call,inv(Entry_Call_out,Call, Inv_aux)):-
    number(Non_loop),
    loop_ph(Head,(Non_loop,RefCnt),Call,Cs,_,_),!,
    compute_relation2entry_invariant(Chain,RefCnt,Entry_Call,inv(Entry_Call_out,Head, Inv)),
  
    Entry_Call_out=..[_|Vars1],
    Call=..[_|Vars2],
    nad_glb(Inv,Cs,Cs_1),
    append(Vars1,Vars2,Vars),
    nad_project_group(Vars,Cs_1,Inv_aux),
    add_relation2entry_invariant(Entry_Call_out,([Non_loop|Chain],RefCnt),inv(Entry_Call_out,Head, Inv)),
    add_relation2entry_invariant_aux(Entry_Call_out,([Non_loop|Chain],RefCnt),inv(Entry_Call_out,Call, Inv_aux)).
%For the leave
compute_relation2entry_invariant([Phase|Chain],RefCnt,Entry_Call,none):-
    number(Phase),!,
    compute_relation2entry_invariant(Chain,RefCnt,Entry_Call,inv(Entry_Call_out,Head_out, Inv)),
    add_relation2entry_invariant(Entry_Call_out,([Phase|Chain],RefCnt),inv(Entry_Call_out,Head_out, Inv)).

% an iterative phase that is not the initial one
% we start  with the invariant of the suffix, we apply the transitive closure to obtain
% the return value and the transitive reflexive closure to obtain the invariant
compute_relation2entry_invariant([Phase|Chain],RefCnt,Entry_Call,inv(Head_aux,Call2, Inv_aux)):-!,
    copy_term(Entry_Call,Head_aux),
    compute_relation2entry_invariant(Chain,RefCnt,Head_aux,inv(Head_aux,Call,Inv_0)),

	phase_transitive_closure(Phase,RefCnt,Call,Call2,Cs_transitive),
	get_phase_star(Call,Call2,Phase,Cs_star),
	Call2=..[_|C2vars],
	Head_aux=..[_|Evars],
	append(Evars,C2vars,Resulting_vars),
	nad_glb(Cs_star,Inv_0,Inv_1),
	nad_glb(Cs_transitive,Inv_0,Inv_2),
	nad_project_group(Resulting_vars,Inv_1,Inv),
	nad_project_group(Resulting_vars,Inv_2,Inv_aux),
	
    add_relation2entry_invariant(Head_aux,([Phase|Chain],RefCnt),inv(Head_aux,Call2, Inv)),
    add_relation2entry_invariant_aux(Head_aux,([Phase|Chain],RefCnt),inv(Head_aux,Call2, Inv)).
  
        
% apply a set of loops to a relation2entry_invariant until a fixpoint is reached
relation2entry_invariant_fixpoint(Count,inv(Entry_inv,Head_inv,Inv),Loops,inv(Entry_out,Head_out,Inv_out)):-
	widening_frequency(Widening_freq),
	apply_loops(Loops,inv(Entry_inv,Head_inv,Inv),Call,Cs_list),
	nad_list_lub(Cs_list,Inv_1),


	Head_inv=Call,
	Entry_inv=..[_|Vars1],
	Call=..[_|Vars2],
	append(Vars1,Vars2,Vars),
	nad_lub(Vars, Inv, Vars, Inv_1, Vars, JoinInv),
	(nad_entails(Vars, JoinInv, Inv)->
	   inv(Entry_out,Head_out,Inv_out)=inv(Entry_inv,Head_inv,JoinInv)
	;
	 (Count>=Widening_freq ->
%	   copy_term((Vars,Inv,JoinInv),(Varsp,Invp,JoinInvp)),
%	   numbervars(Varsp,0,_),
%	   from_list_sl(Invp,Invp_set),from_list_sl(JoinInvp,JoinInvp_set),
%	   difference_sl(Invp_set,JoinInvp_set,Initial_cs),
%	   difference_sl(JoinInvp_set,Invp_set,Final_cs),
%	   format('Loosing precission here:~p~n->~p~n',[Initial_cs,Final_cs]),
	   nad_widen(Vars,Inv,JoinInv,Vars,NewInv),
	   Count1=0
	 ;
	  NewInv=JoinInv,
	  Count1 is Count+1
	 ),
	 relation2entry_invariant_fixpoint(Count1,inv(Entry_inv,Head_inv,NewInv),Loops,inv(Entry_out,Head_out,Inv_out))
	).

apply_loops([],_,_,[]).
apply_loops([(Head_loop,Call_loop,Cs_loop)|Loops],inv(Entry_inv,Head_inv,Inv),Call,[Cs|Cs_list]):-
	copy_term(loop(Head_loop,Call_loop,Cs_loop),loop(Head_inv,Call,Cs_aux)),
	nad_glb(Inv,Cs_aux,Cs_context),
	Entry_inv=..[_|Vars1],
	Call=..[_|Vars2],
	append(Vars1,Vars2,Vars),
	nad_project_group(Vars,Cs_context,Cs),
	apply_loops(Loops,inv(Entry_inv,Head_inv,Inv),Call,Cs_list).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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
	   retract(chain(Entry_Call,RefCnt,Chain))
	;
	\+compute_forward_invariant(Chain,RefCnt,Entry_Call,_),
	  retract(chain(Entry_Call,RefCnt,Chain))
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
    forward_invariant_fixpoint(0,inv(Entry_Call,Inv_0),Loops,inv(Entry_Call,Inv_aux)),
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
    forward_invariant_fixpoint(0,inv(Entry_Call,Inv_0),Loops, inv(Entry_Call, Inv_aux)),
    apply_loops_external(Loops,inv(Entry_Call,Inv_aux),Entry_call2,Cs_list),
    nad_list_lub(Cs_list,Inv_out),
    Entry_call2=Entry_Call,
   (nad_is_bottom(Inv_out)->
        assert(unfeasible_chain_suffix(Entry_Call,RefCnt,[Phase|Chain])),
        fail
     ;
        add_forward_invariant(Entry_Call,([Phase|Chain],RefCnt), Inv_aux)
     ).


%subsequent optional iterations
forward_invariant_fixpoint(Count,inv(Head_inv,Inv),Loops,inv(Entry_out,Inv_out)):-
	widening_frequency(Widening_freq),
	apply_loops_external(Loops,inv(Head_inv,Inv),Call,Cs_list),
	%nad_lubs_group(Cs_list,Inv_1),
	nad_list_lub(Cs_list,Inv_1),
	Head_inv=Call,
	Call=..[_|Vars],
	nad_lub(Vars, Inv, Vars, Inv_1, Vars, JoinInv),
	(nad_entails(Vars, JoinInv, Inv)->
	   inv(Entry_out,Inv_out)=inv(Head_inv,JoinInv)
	;
	 (Count>=Widening_freq ->
	   nad_widen(Vars,Inv,JoinInv,Vars,NewInv),
	   Count1=0
	 ;
	  NewInv=JoinInv,
	  Count1 is Count+1
	 ),
	 forward_invariant_fixpoint(Count1,inv(Head_inv,NewInv),Loops,inv(Entry_out,Inv_out))
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
        relation2entry_invariant_fixpoint(0,inv(Head,Call,Inv_0),Loops,inv(Entry_out,Call_out, Trans_closure)),
        add_phase_transitive_closure(Phase,RefCnt,Entry_out,Call_out,Trans_closure).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! get_phase_star(+Head:term,+Call:term,+Phase:phase,-Cs_star:polyhedron) is det
% computes (if it hasn't been computed before) the transitive reflexive closure of the phase Phase in terms of Head and Call
get_phase_star(Head,Call,Phase,Cs_star):-
	phase_transitive_star_closure(Phase,_RefCnt,Head,Call,Cs_star),!.
	
	
get_phase_star(Head,Call,Phase,Cs_star):-
	phase_transitive_closure(Phase,RefCnt,Head,Call,Cs_transitive),
	Head=..[_|Evars],Call=..[_|Cvars],
	add_equality_constraints(Evars,Cvars,[], Eq_cs),
	nad_list_lub([Eq_cs,Cs_transitive],Cs_star),
	assert(phase_transitive_star_closure(Phase,RefCnt,Head,Call,Cs_star)).



