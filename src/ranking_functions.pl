/**  <module>  ranking_functions

This module computes ranking functions of cost equations and checks their  
mutual dependencies in order to obtain lexicographic ranking functions.
These ranking functions are used to prove termination.


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
:- module(ranking_functions,[init_ranking_functions/0,
				 clean_ranking_functions/1,
			     find_ranking_functions/2,
			     ranking_function/4,
			     partial_ranking_function/7
			     ]).

:- use_module(db,[loop_ph/6,phase_loop/5,get_input_output_vars/3]).
:- use_module('refinement/loops',[get_extended_phase/2]).	

:- use_module('refinement/chains',[chain/3,get_reversed_chains/3]).	  
:- use_module('refinement/invariants',[
				forward_invariant/4,
		      get_context_insensitive_forward_invariant/3]).	
:- use_module('IO/params',[get_param/2]).
:- use_module('utils/cofloco_utils',[
						tuple/3,
						repeat_n_times/3,
						assign_right_vars/3,
						write_sum/2,
						write_le_internal/2,
						normalize_constraint/2]).
:- use_module(stdlib(linear_expression),[
						write_le/2,
						multiply_le/3,
						parse_le/2,
						parse_le_fast/2]).													
:- use_module(stdlib(numeric_abstract_domains),[nad_project/3,nad_minimize/3,nad_maximize/3,
						nad_consistent_constraints/1,
						nad_entails/3, nad_lub/6,nad_list_lub/2,
						nad_widen/5, nad_false/1,
						nad_all_ranking_functions_PR/4,
						nad_all_ranking_functions_MS/4,
						nad_glb/3]).						
:- use_module(stdlib(fraction),[leq_fr/2,negate_fr/2]).						
:- use_module(stdlib(set_list)).
:- use_module(stdlib(multimap),[
    empty_mm/1,
    put_mm/4]).
:-use_module(library(apply_macros)).
:-use_module(library(lists)).   
%! ranking_function(Head:term,Chain_prefix:chain_inverse_prefix,Phase:phase,RF:linear_expression)
% stores a ranking function of the phase Phase that is reached after the pefix Chain_prefix and belongs SCC Head
% if Chain_prefix is not specified, the ranking function is valid for all prefixes that contain
% the phase
:- dynamic ranking_function/4.


%! partial_ranking_function(Head:term,Chain_prefix:chain_inverse_prefix,Phase:phase,Loops:list(equation_id),RF:linear_expression,Deps:list(equation_id),Deps_type:list(flags))
% stores a ranking function of the loops Loops contained in phase Phase
% that is reached after the pefix Chain_prefix and belongs SCC Head.
%
% If Chain_prefix is not specified, the partial ranking function is valid for
% all  prefixes that contain the phase.
%
%Deps  store the loops that can increase the value of the ranking function
%Deps_type specifies how the value is increased:
%  * a fraction: the ranking function can be incremented in that magnitude
%  * unknown: the ranking function might be "restarted"
:- dynamic partial_ranking_function/7.

%! computed_ranking_functions(Head:term,Chain:chain,Phase:phase)
% record that the inference of ranking functions for the corresponding Phase of Chain in Head has been already performed
:-dynamic computed_ranking_functions/3.
:-dynamic computed_partial_ranking_functions/3.
%! init_ranking_functions is det
%clean the stored ranking functions
init_ranking_functions:-
	retractall(ranking_function(_,_,_,_)),
	retractall(partial_ranking_function(_,_,_,_,_,_,_)),
	retractall(computed_ranking_functions(_,_,_)),
	retractall(computed_partial_ranking_functions(_,_,_)).

clean_ranking_functions(Head):-
	retractall(ranking_function(Head,_,_,_)),
	retractall(partial_ranking_function(Head,_,_,_,_,_,_)),
	retractall(computed_ranking_functions(Head,_,_)),
	retractall(computed_partial_ranking_functions(Head,_,_)).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! find_ranking_functions(+Head:term,+RefCnt:int) is det
% find and store all ranking functions of SCC Head
find_ranking_functions(Head,RefCnt):-
	chain(Head,RefCnt,Chain),
	get_reversed_chains([],Chain,Chains_rev),
	maplist(find_chain_ranking_functions_aux(Head),Chains_rev),
	fail.
find_ranking_functions(_,_).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
find_chain_ranking_functions_aux(Head,Chain):-
	find_chain_ranking_functions(Chain,Head).
%! find_chain_ranking_functions(Chain_rev:chain_rev,Head:term) is det
% infer ranking functions for the iterative phases of a chain
find_chain_ranking_functions([],_).
find_chain_ranking_functions([Non_loop|Rec_elems],Head):-
		number(Non_loop),!,
		find_chain_ranking_functions(Rec_elems,Head).

find_chain_ranking_functions([Phase|Rec_elems],Head):-
		get_context_insensitive_forward_invariant(Head,Phase,Inv),
	    forward_invariant(Head,([Phase|Rec_elems],_),_,Inv_sensitive),
		compute_phase_rfs(Head,[Phase|Rec_elems],Phase,Inv,Inv_sensitive),
		compute_phase_partial_rfs(Head,[Phase|Rec_elems],Phase,Inv,Inv_sensitive),
		find_chain_ranking_functions(Rec_elems,Head).

%! compute_phase_rfs(Head:term,Chain_prefix:chain_inverse_prefix,Phase:phase,Inv:polyhedron) is det 
% try to compute ranking functions valid for all cost equations in Phase using the invariant Inv
compute_phase_rfs(Head,Chain_prefix,Phase,_Inv,_):-
	computed_ranking_functions(Head,Chain_prefix,Phase),!.

% we try to infer a universal rf for the phase 
compute_phase_rfs(Head,_Chain_prefix,Phase,Inv,_):-
	%we haven't computed any rf for this phase
	\+computed_ranking_functions(Head,_,Phase),
	phase_loop(Phase,_,Head,Call,Cs),
	nad_glb(Cs,Inv,Cs_1),
	compute_iterations_ubs( Head, Call, Cs_1, Iter_Ubs),
	(Iter_Ubs\=[] 
	 ;
	 get_param(context_sensitive,[Sensitivity]),
	 Sensitivity =< 1
	),!,
	maplist(add_ranking_function(Head,_,Phase),Iter_Ubs),
	assert(computed_ranking_functions(Head,_,Phase)).

%If we failed to compute a universal ranking function, we try to compute ranking functions using the given chain invariant
compute_phase_rfs(Head,Chain_prefix,Phase,_,Inv_sensitive):-
	   get_param(context_sensitive,[Sensitivity]),Sensitivity > 1,
       phase_loop(Phase,_,Head,Call,Cs),
       nad_glb(Cs,Inv_sensitive,Cs_1),
       compute_iterations_ubs( Head, Call, Cs_1, Iter_Ubs),
       maplist(add_ranking_function(Head,Chain_prefix,Phase),Iter_Ubs),
       assert(computed_ranking_functions(Head,Chain_prefix,Phase)).


%! compute_phase_partial_rfs(Head:term,Chain_prefix:chain_inverse_prefix,Phase:phase,Inv:polyhedron) is det 
% try to compute ranking functions for each cost equation in the phase and infer
% how these ranking functions can be increased in other cost equations (the dependencies)
compute_phase_partial_rfs(Head,Chain_prefix,Phase,_Inv,_):-
	computed_partial_ranking_functions(Head,Chain_prefix,Phase),!.

% we try to compute universal ranking functions first. If there is a cost equation that does not
% have any universal ranking function we fail and use the invariant.
%
% This is not perfect because we might have a ranking function in every cost equation of a phase and still have a cyclic dependency
% but it's a decent heuristic.
compute_phase_partial_rfs(Head,Chain_prefix,Phase,Inv,_):-
	%we haven't computed any rf for this phase
	\+computed_partial_ranking_functions(Head,_,Phase),
	empty_mm(Empty_map),
	%compute without invariant
	get_extended_phase(Phase,Extended_phase),
	foldl(compute_1_loop_rfs(Head,Call,Inv),Extended_phase,Empty_map,Initial_map),
	(
		loops_covered(Extended_phase,Initial_map)
	;
		get_param(context_sensitive,[Sensitivity]),
	    Sensitivity =< 1
	),!,
	% exclude ranking functions that are general
	exclude(covered_by_rf_map(Head,Extended_phase,Chain_prefix),Initial_map,Initial_map_filtered),
	%the initial dependencies are all phases except the covered ones
	maplist(get_initial_deps(Extended_phase),Initial_map_filtered,Init_deps),
	maplist(check_lexicographic_deps_aux(Head,Call,Inv),Initial_map_filtered,Init_deps,Deps,Type_deps),
	maplist(add_partial_ranking_function_aux(Head,_,Phase),Initial_map_filtered,Deps,Type_deps),
	assert(computed_partial_ranking_functions(Head,_,Phase)).
	

compute_phase_partial_rfs(Head,Chain_prefix,Phase,_Inv,Inv_sensitive):-
       empty_mm(Empty_map),
       %initial map with the ranking functions and the loops they cover
       get_extended_phase(Phase,Extended_phase),
       foldl(compute_1_loop_rfs(Head,Call,Inv_sensitive),Extended_phase,Empty_map,Initial_map),
       Chain_saved=Chain_prefix,
       % exclude ranking functions that are general
       exclude(covered_by_rf_map(Head,Extended_phase,Chain_prefix),Initial_map,Initial_map_filtered),
       %the initial dependencies are all phases except the covered ones
       maplist(get_initial_deps(Extended_phase),Initial_map_filtered,Init_deps),
       maplist(check_lexicographic_deps_aux(Head,Call,Inv_sensitive),Initial_map_filtered,Init_deps,Deps,Type_deps),
       maplist(add_partial_ranking_function_aux(Head,Chain_saved,Phase),Initial_map_filtered,Deps,Type_deps),
       assert(computed_partial_ranking_functions(Head,Chain_saved,Phase)).


loops_covered(Loops,Multimap):-
	maplist(tuple,_,Sets,Multimap),
	from_list_sl(Loops,Loops_set),
	unions_sl(Sets,Covered_loops),
	difference_sl(Loops_set,Covered_loops,[]).	

get_extended_loop(Head,Loop:1,Call,Cs_loop):-
	loop_ph(Head,(Loop,_),[Call],Cs_loop,_,_),!.
	
get_extended_loop(Head,Loop:N,Call,Cs_loop1):-
	loop_ph(Head,(Loop,_),Calls,Cs_loop,_,_),
	nth1(N,Calls,Call),
	term_variables((Head,Call),Vars),
	nad_project(Vars,Cs_loop,Cs_loop1),!.

	
compute_1_loop_rfs(Head,Call,Inv,Extended_Loop,Map_in,Map_out):-
	get_extended_loop(Head,Extended_Loop,Call,Cs_loop),
	nad_glb(Cs_loop,Inv,Cs_loop1),
	compute_iterations_ubs( Head, Call, Cs_loop1, Rfs),
	foldl(add_rf_2_map(Extended_Loop),Rfs,Map_in,Map_out).

add_rf_2_map(Extended_Loop,Rf,Map_in,Map_out):-
	put_mm( Map_in, Rf, Extended_Loop, Map_out).
	
get_initial_deps(Phase,(_Rf,Covered),Deps):-
	difference_sl(Phase,Covered,Deps).
	
covered_by_rf_map(Head,Phase,Chain_prefix,(Rf,_Values)):-
	covered_by_rf(Head,Phase,Chain_prefix,Rf).
	
check_lexicographic_deps_aux(Head,Call,Inv,(Rf,_Covered),Init_deps,Deps,Type_deps):-
	check_lexicographic_deps(Init_deps,Head,Call,Inv,Rf,Deps,Type_deps).
		
add_partial_ranking_function_aux(Head,Chain,Phase,(Rf,Covered),Deps,Type_deps):-
	add_partial_ranking_function(Head,Chain,Phase,Covered,Rf,Deps,Type_deps).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



%! check_lexicographic_deps(+Loops:list(equation_id),+Head:term,+Call:term,+Rf:linear_expression,-Deps_out:list(equation_id),-Type_deps_out:list(flag)) is det
% given a ranking function Rf, infer which other cost equations can increase Rf and by how much
% Type_deps_out is a list of flags that can be an integer or unknown
check_lexicographic_deps([],_Head,_Call,_,_Rf,[],[]).
check_lexicographic_deps([Extended_Loop|Loops],Head,Call,Inv,Rf,Deps_out,Type_deps_out):-
	get_extended_loop(Head,Extended_Loop,Call,Cs_loop),
	nad_glb(Cs_loop,Inv,Cs_loop1),
	check_increment(Head,Call,Cs_loop1,Rf,Inc),
	( leq_fr(Inc,0) ->
	    Deps_out=Deps_out_aux,
	    Type_deps_out=Type_deps_out_aux
	  ;
	    Deps_out=[Extended_Loop|Deps_out_aux],
	    Type_deps_out=[Inc|Type_deps_out_aux]
	),!,
	check_lexicographic_deps(Loops,Head,Call,Inv,Rf,Deps_out_aux,Type_deps_out_aux).

check_lexicographic_deps([Extended_Loop|Loops],Head,Call,Inv,Rf,[Extended_Loop|Deps_out],[unknown|Type_deps_out]):-
	check_lexicographic_deps(Loops,Head,Call,Inv,Rf,Deps_out,Type_deps_out).

%! check_increment(+Head:term,+Call:term,+Cs:polyhedron,+F:linear_expression,-Delta:fraction) is semidet
% try to find a costant of how much a ranking function can be increased in the loop defined by Head,Call and Cs
check_increment(Head,Call,Cs,Rf,Delta) :-
	copy_term([Head,Rf],[Call,Rfp]),
	normalize_constraint( D=Rf-Rfp ,Constraint),
	Cs_1 = [ Constraint | Cs],
	nad_minimize(Cs_1,[D],[Delta1]),
	negate_fr(Delta1,Delta).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

add_ranking_function(Head,Chain_prefix,Phase,Rf) :-
	parse_le_fast(Rf,Lin_exp),
	add_ranking_function_1(Head,Chain_prefix,Phase,Lin_exp).

add_ranking_function_1(Head,Chain_prefix,Phase,Rf):-	
	ranking_function(Head,Chain_prefix,Phase,RF_1),
	RF_1==Rf,!.

add_ranking_function_1(Head,Chain_prefix,Phase,RF) :-
	assertz(ranking_function(Head,Chain_prefix,Phase,RF)).

add_partial_ranking_function(Head,Chain_prefix,Phase,Loop,RF,Deps,Deps_type) :-
	parse_le_fast(RF,Lin_exp),
	add_partial_ranking_function_1(Head,Chain_prefix,Phase,Loop,Lin_exp,Deps,Deps_type).
	

add_partial_ranking_function_1(Head,Chain_prefix,Phase,Loop,RF,Deps,Deps_type) :-
	partial_ranking_function(Head,Chain_prefix,Phase,Loop,RF2,Deps,Deps_type),
	RF==RF2,!.

add_partial_ranking_function_1(Head,Chain_prefix,Phase,Loop,RF,Deps,Deps_type) :-
	assertz(partial_ranking_function(Head,Chain_prefix,Phase,Loop,RF,Deps,Deps_type)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



compute_iterations_ubs( Head,Call,Phi, Rfs2) :-
	 get_input_output_vars(Head,EntryVars,_),
	 get_input_output_vars(Call,ExitVars,_),
	 append(EntryVars,ExitVars,Vars),
	 nad_project(Vars,Phi,Phi_reduced),
	 nad_all_ranking_functions_PR(Phi_reduced,EntryVars,ExitVars,Rfs),
	 compute_offsets(Rfs,Phi,Rfs1),
     maplist(adapt_fraction,Rfs1,Rfs2).

adapt_fraction(Rf,Rf_2):-
	\+var(Rf),
	Rf=Rf_1/Div,!,
	parse_le(Rf_1,Rf_lin_exp),
	multiply_le(Rf_lin_exp,1/Div,Rf_lin_exp_2),
	write_le_internal(Rf_lin_exp_2,Rf_2).

adapt_fraction(Rf,Rf).


compute_offsets([],_,[]).
compute_offsets([Rf/D|Rfs],Cs,[Rf_1/D|Rfs_1]):-!,
	compute_offset(Rf,Cs,Rf_1),
	compute_offsets(Rfs,Cs,Rfs_1).
compute_offsets([Rf|Rfs],Cs,[Rf_1|Rfs_1]):-
	compute_offset(Rf,Cs,Rf_1),
	compute_offsets(Rfs,Cs,Rfs_1).

compute_offset(Rf,Cs,Rf_1):-
	Cs_1 = [D0=Rf | Cs],
	nad_minimize(Cs_1,[D0],[Val]),
	Offset is ceiling(-Val+1),
	Rf_1=Rf+Offset.

covered_by_rf(Head,Phase,Chain_prefix,Rf):-
	ranking_function(Head,Chain_prefix,Phase,Rf1),
	Rf1==Rf.