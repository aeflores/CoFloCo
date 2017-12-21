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
:- module(ranking_functions,[
			     find_loops_ranking_functions/3,
			     prove_phases_termination/4
			     ]).

:- use_module('refinement/loops',[
	loop_head/2,
	loop_add_property/4,
	loop_get_property/3,
	loops_get_list_fresh_with_id/3,
	loops_apply_to_each_loop/3,
	loops_split_multiple_loops_with_id/2,
	loops_split_multiple_loops/2]).

:- use_module('refinement/chains',[
	phase_get_property/3,
	phase_add_property/4]).	  

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
:- use_module(stdlib(utils),[ut_flat_list/2]).
:- use_module(stdlib(multimap),[
    empty_mm/1,
    put_mm/4]).
:-use_module(library(apply_macros)).
:-use_module(library(lists)).   
:-use_module(library(lambda)).   


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! find_ranking_functions(+Head:term,+RefCnt:int) is det
% find and store all ranking functions of SCC Head

find_loops_ranking_functions(IOvars,Loops,Loops2):-
	loops_apply_to_each_loop(ranking_functions:find_loop_ranking_functions(IOvars),Loops,Loops2).

find_loop_ranking_functions(IOvars,Loop,Annotated_loop):-
	loops_split_multiple_loops([Loop],Splitted_loops),
	length(Splitted_loops,N),
	foldl(find_linear_ranking_function(IOvars),Splitted_loops,(N,[]),(_N,Ranking_functions)),
	loop_add_property(Loop,ranking_functions,ranking_functions(Ranking_functions),Annotated_loop).

find_linear_ranking_function(IOvars,linear_loop(Head,Call,Inv_loop),(N,Accum),(N1,[(N,Rfs)|Accum])):-
	find_linear_ranking_function_1(IOvars,linear_loop(Head,Call,Inv_loop),Rfs),
	N1 is N-1.
	
find_linear_ranking_function_1(IOvars,linear_loop(Head,Call,Phi),Rfs_set):-
	 copy_term(IOvars,ioVars(Head,EntryVars,_)),
	 copy_term(IOvars,ioVars(Call,ExitVars,_)),
	 append(EntryVars,ExitVars,Vars),
	 nad_project(Vars,Phi,Phi_reduced),
	 nad_all_ranking_functions_PR(Phi_reduced,EntryVars,ExitVars,Rfs),
	 compute_offsets(Rfs,Phi,Rfs1),
     maplist(adapt_fraction,Rfs1,Rfs2),
     from_list_sl(Rfs2,Rfs_set).

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
	(Offset=0->
		Rf_1=Rf
	;
		Rf_1=Rf+Offset
	).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

prove_phases_termination(chains(Phases,Chains),IOvars,Loops,chains(Phases2,Chains)):-
	maplist(prove_phase_termination(IOvars,Loops),Phases,Phases2).
	
prove_phase_termination(_IOvars,_Loops,phase(Non_iterative,Properties),Phase2):-
	number(Non_iterative),!,
	phase_add_property(phase(Non_iterative,Properties),termination,terminating(trivial),Phase2).

prove_phase_termination(IOvars,_Loops,Phase,Phase3):-
	phase_get_property(Phase,phase_loop,phase_loop(Head,Call,Cs)),
	find_linear_ranking_function_1(IOvars,linear_loop(Head,Call,Cs),Rfs_phase),
	Rfs_phase\=[],!,
	once(member(Rf,Rfs_phase)),
	phase_add_property(Phase,ranking_functions,ranking_functions(Head,Rfs_phase),Phase2),
	phase_add_property(Phase2,termination,terminating(Head,[rf_covers(Rf,all)]),Phase3).

prove_phase_termination(_IOvars,Loops,phase(Phase,Properties),Phase2):-
	loops_get_list_fresh_with_id(Loops,Phase,Phase_loops),
	%unify all heads
	maplist(Head+\Loop_l^(
					Loop_l=(_,Loop_l2),
					loop_head(Loop_l2,Head)
					),Phase_loops),
	%get ranking functions
	maplist(\LoopWithId^Rfs^(
		LoopWithId=(_,Loop),
		loop_get_property(Loop,ranking_functions,ranking_functions(Rfs))
		),Phase_loops,Ranking_functions),
	loops_split_multiple_loops_with_id(Phase_loops,Splitted_loops_rev),
	reverse(Splitted_loops_rev,Splitted_loops),
	ut_flat_list(Ranking_functions,Ranking_flat),
	
	%put them together with the splitted loops
	maplist(\Linear_loop^Pair^Joined_loop^(
		Linear_loop=(IdLoop:N,Lin_loop),
		Pair=(N,Rfs_loop),
		Joined_loop=joined_loop(IdLoop:N,Lin_loop,Rfs_loop)
	),
		Splitted_loops,Ranking_flat,Joined_loops),
	find_lexicographical_proof(Head,Joined_loops,Termination),
	phase_add_property(phase(Phase,Properties),termination,Termination,Phase2).
	
find_lexicographical_proof(Head,Joined_loops,Proof):-
	maplist(get_loop_ids,Joined_loops,Ids),
	from_list_sl(Ids,Id_set),
	foldl(get_all_rfs,Joined_loops,[],All_rfs),
	maplist(get_initial_rf_dependency_map(Id_set),All_rfs,Initial_map),
	foldl(compute_loop_dependencies,Joined_loops,Initial_map,Dependency_map),
	maplist(get_dependency_pairs,Dependency_map,Dependency_pairs),
	keysort(Dependency_pairs,Sorted_pairs),
	find_lexicographic_proof_1(Sorted_pairs,Id_set,[],Phase_rf),
	(Phase_rf=[not_covered(_)|_]->
		Proof=non_terminating(Head,Phase_rf)
		;
		Proof=terminating(Head,Phase_rf)
	).

get_loop_ids(joined_loop(Id,_,_),Id).
get_all_rfs(joined_loop(_Id,_,Rfs),Accum,Accum2):-
	union_sl(Rfs,Accum,Accum2).

get_initial_rf_dependency_map(Idset,Rf,cover_depend(Rf,[],Idset)).

compute_loop_dependencies(Joined_loop,Cover_info,Cover_info2):-
	maplist(update_cover_info(Joined_loop),Cover_info,Cover_info2).
	
update_cover_info(joined_loop(Id,Loop,Rfs),cover_depend(Rf,Covered,Depend),cover_depend(Rf,Covered1,Depend1)):-
	(contains_sl(Rfs,Rf); is_ranking_function(Loop,Rf)),
	!,
	insert_sl(Covered,Id,Covered1),
	remove_sl(Depend,Id,Depend1).

update_cover_info(joined_loop(Id,Loop,_Rfs),cover_depend(Rf,Covered,Depend),cover_depend(Rf,Covered,Depend1)):-
	loop_not_increase(Loop,Rf),!,
	remove_sl(Depend,Id,Depend1).

update_cover_info(_,cover_depend(Rf,Covered,Depend),cover_depend(Rf,Covered,Depend)).


%! check_increment(+Head:term,+Call:term,+Cs:polyhedron,+F:linear_expression,-Delta:fraction) is semidet
% try to find a costant of how much a ranking function can be increased in the loop defined by Head,Call and Cs
loop_not_increase(linear_loop(Head,Call,Inv_loop),Rf):-
	copy_term([Head,Rf],[Call,Rfp]),
	normalize_constraint( Rf-Rfp >=0 ,Constraint),
	term_variables((Head,Call),Vars),
	nad_entails(Vars,Inv_loop,[Constraint]).

is_ranking_function(linear_loop(Head,Call,Inv_loop),Rf):-
	copy_term([Head,Rf],[Call,Rfp]),
	normalize_constraint( Rf-Rfp >=1 ,Constraint),
	term_variables((Head,Call),Vars),
	nad_entails(Vars,Inv_loop,[Constraint]),
	normalize_constraint( Rf >=0 ,Constraint2),
	nad_entails(Vars,Inv_loop,[Constraint2]).
	
get_dependency_pairs(cover_depend(Rf,Covered,Depend),N-cover_depend(Rf,Covered,Depend)):-
	length(Depend,N).
	

%if there are no loops left, terminate
find_lexicographic_proof_1(_Sorted_structure,[],Term_arg,Term_arg):-!.
%if there are loops left but not ranking functions, return the remaining loops with a 'no' flag
find_lexicographic_proof_1([],Rem_lg,Rf_accum,[not_covered(Rem_lg)|Rf_accum]):-!.
% if there is ranking function with 0 dependencies, remove the loops involved
% and decrease the dependencies accordingly
find_lexicographic_proof_1([0-cover_depend(Rf,Loops,_Dep_set)|Deps],Rem_lg,Rf_accum,Term_arg):-!,
	difference_sl(Rem_lg,Loops,Rem_lg1),
	prune_loops_structure(Deps,Loops,Deps1),
	prune_deps_structure(Deps1,Loops,Deps2),
	find_lexicographic_proof_1(Deps2,Rem_lg1,[rf_covers(Rf,Loops)|Rf_accum],Term_arg).

%if the next ranking function has dependencies:
% * try to reorder the ranking functions and continue
% * if even so all ranking functions have dependencies, return 'no'
find_lexicographic_proof_1([N-cover_depend(Rf,Loop,Dep_set)|Deps],Rem_lg,Rf_accum,Term_arg):-
	N>0,
	keysort([N-cover_depend(Loop,Rf,Dep_set)|Deps],[N2-cover_depend(Rf2,Loop2,Dep_set2)|Deps2]),
	(N2=0->
	 find_lexicographic_proof_1([N2-cover_depend(Rf2,Loop2,Dep_set2)|Deps2],Rem_lg,Rf_accum,Term_arg)
	;
	 Term_arg=[not_covered(Rem_lg)|Rf_accum]
	).

prune_loops_structure([],_,[]).
prune_loops_structure([N-cover_depend(Rf,Loops1,Dep_set)|Deps],Loops2,Deps1):-
	difference_sl(Loops1,Loops2,Rest),
	prune_loops_structure(Deps,Loops2,Deps_aux),
	(Rest\=[]->
	    Deps1=[N-cover_depend(Rf,Loops1,Dep_set)|Deps_aux]
	    ;
	    Deps1=Deps_aux
	    ).
prune_deps_structure([],_,[]).
prune_deps_structure([_-cover_depend(Rf,Loops,Dep_set)|Deps],Loops2,[N2-cover_depend(Rf,Loops,Dep_set2)|Desp1]):-
	difference_sl(Dep_set,Loops2,Dep_set2),
	length(Dep_set2,N2),
	prune_deps_structure(Deps,Loops2,Desp1).	


