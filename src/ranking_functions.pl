/**  <module>  ranking_functions

This module computes ranking functions of cost equations and checks their  
mutual dependencies in order to obtain lexicographic ranking functions



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
			     find_ranking_functions/2,
			     ranking_function/4,
			     partial_ranking_function/7
			     ]).

:- use_module(db,[loop_ph/4,phase_loop/5,eq_ph/7]).
:- use_module('refinement/chains',[chain/3]).		  

:- use_module('IO/params',[get_param/2]).
:- use_module('upper_bounds/constraints_maximization',[maximize_linear_expression_all/4]).
:- use_module('utils/cofloco_utils',[zip_with_op/4,assign_right_vars/3,normalize_constraint/2]).
:- use_module(stdlib(numeric_abstract_domains),[nad_project/3,nad_minimize/3,
						nad_consistent_constraints/1,
						nad_entails/3, nad_lub/6,nad_list_lub/2,
						nad_widen/5, nad_false/1,
						nad_all_ranking_functions_PR/4,
						nad_glb/3]).
:- use_module(stdlib(set_list)).
:- use_module(stdlib(multimap),[
    empty_mm/1,
    put_mm/4]).
    
%! ranking_function(Head:term,Chain:chain,Phase:phase,RF:linear_expression)
% stores a ranking function of the phase Phase that belongs to the Chain and SCC Head
% if Chain is not specified, the ranking function is valid for all chains that contain
% the phase
:- dynamic ranking_function/4.


%! partial_ranking_function(Head:term,Chain:chain,Phase:phase,Loops:list(equation_id),RF:linear_expression,Deps:list(equation_id),Deps_type:list(flags))
% stores a ranking function of the loops Loops contained in phase Phase
% that belongs to the Chain and SCC Head.
%
% If Chain is not specified, the partial ranking function is valid for
% all chains that contain the phase.
%
%Deps  store the loops that can increase the value of the ranking function
%Deps_type specifies how the value is increased:
%  * an integer: the ranking function can be incremented in that magnitude
%  * unknown: the ranking function might be "restarted"
:- dynamic partial_ranking_function/7.

%! computed_ranking_functions(Head:term,Chain:chain,Phase:phase)
% record that the inference of ranking functions for the corresponding Phase of Chain in Head has been already performed
:-dynamic computed_ranking_functions/3.

%! init_ranking_functions is det
%clean the stored ranking functions
init_ranking_functions:-
	retractall(ranking_function(_,_,_,_)),
	retractall(partial_ranking_function(_,_,_,_,_,_,_)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! find_ranking_functions(+Head:term,+RefCnt:int) is det
% find and store all ranking functions of SCC Head
find_ranking_functions(Head,RefCnt):-
	chain(Head,RefCnt,Chain),
	find_chain_ranking_functions(Chain,Head,Chain),
	fail.
find_ranking_functions(_,_).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! find_chain_ranking_functions(Chain:chain,Head:term,Chain:chain) is det
% infer ranking functions for the iterative phases of a chain
% right now we ignore the chain invariants so the ranking functions for a phase are universal
find_chain_ranking_functions([],_,_).
find_chain_ranking_functions([Non_loop|Rec_elems],Head,Chain):-
		number(Non_loop),!,
		find_chain_ranking_functions(Rec_elems,Head,Chain).

find_chain_ranking_functions([Phase|Rec_elems],Head,Chain):-
	    %TODO take the chain into account to get better ranking functions
	    (\+computed_ranking_functions(Head,Chain,Phase)->
		   compute_phase_rfs(Head,Chain,Phase,[]),
		   %maplist(compute_loop_partial_rfs(Head,Chain,Phase,[]),Phase),
		   compute_phase_partial_rfs(Head,Chain,Phase,[]),
		   assert(computed_ranking_functions(Head,_,Phase))
		;
		   true),
		find_chain_ranking_functions(Rec_elems,Head,Chain).

%! compute_phase_rfs(Head:term,Chain:chain,Phase:phase,Inv:polyhedron) is det 
% try to compute ranking functions valid for all cost equations in Phase using the invariant Inv
%For now we ignore the chain and infer generic ranking functions for Phase in any chain (the invariant is empty)
compute_phase_rfs(Head,_,Phase,Inv):-
	phase_loop(Phase,_,Head,Call,Cs),
	nad_glb(Cs,Inv,Cs_1),
	compute_iterations_ubs_without_fractions( Head, Call, Cs_1, Iter_Ubs),
	maplist(add_ranking_function(Head,_,Phase),Iter_Ubs).


%! compute_phase_partial_rfs(Head:term,Chain:chain,Phase:phase,Inv:polyhedron) is det 
% try to compute ranking functions for each cost equation in the phase and infer
% how these ranking functions can be increased in other cost equations (the dependencies)
compute_phase_partial_rfs(Head,Chain,Phase,Inv):-
	empty_mm(Empty_map),
	%initial map with the ranking functions and the loops they cover
	foldl(compute_1_loop_rfs(Head,Call,Inv),Phase,Empty_map,Initial_map),
	% exclude ranking functions that are general
	exclude(covered_by_rf_map(Head,Phase),Initial_map,Initial_map_filtered),
	

	%the initial dependencies are all phases except the covered ones
	maplist(get_initial_deps(Phase),Initial_map_filtered,Init_deps),
	maplist(check_lexicographic_deps_aux(Head,Call),Initial_map_filtered,Init_deps,Deps,Type_deps),
	maplist(add_partial_ranking_function_aux(Head,Chain,Phase),Initial_map_filtered,Deps,Type_deps).


compute_1_loop_rfs(Head,Call,Inv,Loop,Map_in,Map_out):-
	loop_ph(Head,(Loop,_),Call,Cs_loop),
	nad_glb(Cs_loop,Inv,Cs_loop1),
	compute_iterations_ubs_without_fractions( Head, Call, Cs_loop1, Rfs),
	foldl(add_rf_2_map(Loop),Rfs,Map_in,Map_out).

add_rf_2_map(Loop,Rf,Map_in,Map_out):-
	put_mm( Map_in, Rf, Loop, Map_out).
	
get_initial_deps(Phase,(_Rf,Covered),Deps):-
	difference_sl(Phase,Covered,Deps).
	
covered_by_rf_map(Head,Phase,(Rf,_Values)):-
	covered_by_rf(Head,Phase,Rf).
	
check_lexicographic_deps_aux(Head,Call,(Rf,_Covered),Init_deps,Deps,Type_deps):-
	check_lexicographic_deps(Init_deps,Head,Call,Rf,Deps,Type_deps).
		
add_partial_ranking_function_aux(Head,Chain,Phase,(Rf,Covered),Deps,Type_deps):-
	add_partial_ranking_function(Head,Chain,Phase,Covered,Rf,Deps,Type_deps).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



%! check_lexicographic_deps(+Loops:list(equation_id),+Head:term,+Call:term,+Rf:linear_expression,-Deps_out:list(equation_id),-Type_deps_out:list(flag)) is det
% given a ranking function Rf, infer which other cost equations can increase Rf and by how much
% Type_deps_out is a list of flags that can be an integer or unknown
check_lexicographic_deps([],_Head,_Call,_Rf,[],[]).
check_lexicographic_deps([Loop|Loops],Head,Call,Rf,Deps_out,Type_deps_out):-
	loop_ph(Head,(Loop,_),Call,Cs_loop),
	check_increment(Head,Call,Cs_loop,Rf,Inc),
	( Inc =< 0 ->
	    Deps_out=Deps_out_aux,
	    Type_deps_out=Type_deps_out_aux
	  ;
	    Deps_out=[Loop|Deps_out_aux],
	    Type_deps_out=[Inc|Type_deps_out_aux]
	),!,
	check_lexicographic_deps(Loops,Head,Call,Rf,Deps_out_aux,Type_deps_out_aux).

check_lexicographic_deps([Loop|Loops],Head,Call,Rf,[Loop|Deps_out],[unknown|Type_deps_out]):-
	check_lexicographic_deps(Loops,Head,Call,Rf,Deps_out,Type_deps_out).

%! check_increment(+Head:term,+Call:term,+Cs:polyhedron,+F:linear_expression,-Delta:int) is semidet
% try to find a costant of how much a ranking function can be increased in the loop defined by Head,Call and Cs
check_increment(Head,Call,Cs,F,Delta) :-
	normalize_rf(F,Rf),
	copy_term([Head,Rf],[Call,Rfp]),
	Cs_1 = [ D=Rf-Rfp | Cs],
	nad_minimize(Cs_1,[D],[Delta1]),
	Delta is -Delta1.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

add_ranking_function(Head,Chain,Phase,RF) :-
	ranking_function(Head,Chain,Phase,RF_1),
	RF_1==RF,!.

add_ranking_function(Head,Chain,Phase,RF) :-
	assertz(ranking_function(Head,Chain,Phase,RF)),
	copy_term((Head,RF),(PHead,PRF)),
	numbervars(PHead,0,_),
	(get_param(debug,[])->
	 format('~p~n',ranking_function(PHead,Chain,Phase,PRF))
	;
	 true).



add_partial_ranking_function(Head,_,Phase,Loop,RF,Deps,Deps_type) :-
	partial_ranking_function(Head,_,Phase,Loop,RF2,Deps,Deps_type),
	RF==RF2,!.

add_partial_ranking_function(Head,_,Phase,Loop,RF,Deps,Deps_type) :-
	assertz(partial_ranking_function(Head,_,Phase,Loop,RF,Deps,Deps_type)),
	copy_term((Head,RF),(PHead,PRF)),
	numbervars(PHead,0,_),
	(get_param(debug,[])->
	 format('~p~n',partial_ranking_function(PHead,Phase,Loop,PRF,Deps,Deps_type))
	;
	 true).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



compute_iterations_ubs_without_fractions( Head,Call,Phi, Rfs) :-
     pr04_compute_all_rfs_ppl(Head,Call,Phi,Rfs1),
     maplist(remove_fraction,Rfs1,Rfs).

remove_fraction(Rf,Rf_2):-
	\+var(Rf),
	Rf=Rf_1/_,!,
	remove_fraction(Rf_1,Rf_2).
remove_fraction(Rf,Rf).

pr04_compute_all_rfs_ppl(Head, Body, Cs, Rfs_1) :-
	Head=..[_|EntryVars],
	Body=..[_|ExitVars],
	nad_all_ranking_functions_PR(Cs,EntryVars,ExitVars,Rfs),
	compute_offsets(Rfs,Cs,Rfs_1).

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
%	(Offset =< 0 ->
%	   Rf_1=Rf
%	   ;
	   Rf_1=Rf+Offset.
%	).
	
	
normalize_rf(F,FN-Constant) :-
	normalize_constraint(F>=0,FN>=Constant).

covered_by_rf(Head,Phase,Rf):-
	ranking_function(Head,_,Phase,Rf1),
	Rf1==Rf.