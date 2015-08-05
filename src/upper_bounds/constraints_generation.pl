/** <module> constraints_generation

This module generates new constraints for the iteration variables of a phase based on 
the ranking functions.

    
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
:- module(constraints_generation,[
		add_phase_lower_bounds/6,
		add_phase_upper_bounds/6
	]).

:- use_module(constraints_maximization,[
				max_min_linear_expression_all/5]).		      
:- use_module('../db',[phase_loop/5,loop_ph/6]).
:-use_module('../refinement/invariants',[get_phase_star/4]).
:- use_module('../ranking_functions',[
				      ranking_function/4,
				      partial_ranking_function/7]).
:- use_module('../IO/params',[get_param/2]).

:- use_module('../utils/cofloco_utils',[
		    tuple/3,
		    normalize_constraint/2,
		    bagof_no_fail/3,
		    repeat_n_times/3]).

:- use_module('../utils/cost_expressions',[
						  normalize_le/2,
					      cexpr_simplify_ctx_free/2,
					      is_linear_exp/1]).
:- use_module('../utils/cost_structures',[
			cstr_name_aux_var/1,
			cstr_get_it_name/2,
			cstr_generate_top_exp/3
			]).

:- use_module(stdlib(utils),[ut_flat_list/2,ut_split_at_pos/4]).
:- use_module(stdlib(set_list)).
:- use_module(stdlib(list_map),[lookup_lm/3]).
:- use_module(stdlib(fraction),[min_fr/3,max_fr/3,negate_fr/2]).
:- use_module(stdlib(numeric_abstract_domains),[nad_entails/3,
						nad_list_lub/2,
						nad_list_glb/2,
						nad_lub/6,
						nad_glb/3,
						nad_maximize/3,
						nad_minimize/3,
						nad_consistent_constraints/1]).


	
%rf_limit(-N:int) is det
% stablish the maximum number of ranking functions for the whole phase that are to be considered
rf_limit(N):-
	get_param(n_rankings,[N]).
	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

add_phase_upper_bounds(Head,Call,Phase,_Chain,Top,Aux):-
	rf_limit(Max),
	get_ranking_functions_constraints(Max,Head,Call,Phase,Chain,Top1,Aux1),
	get_partial_ranking_functions_constraints(Max,Head,Call,Phase,Chain,Top2,Aux2),
	append(Top1,Top2,Top),
	append(Aux1,Aux2,Aux).
	


get_ranking_functions_constraints(Max,Head,Call,Phase,Chain,Top,[]):-
		bagof_no_fail(Rf,
	ranking_function(Head,Chain,Phase,Rf)
	   ,Rfs),
	   ut_split_at_pos(Rfs,Max,Rfs_selected,_),
	   maplist(get_difference_version(Head,Call),Rfs_selected,Rfs_diff),
	   maplist(cstr_get_it_name,Phase,Bounded),
	   append(Rfs_selected,Rfs_diff,Rfs_total),
	   maplist(cstr_generate_top_exp(Bounded),Rfs_total,Top).



get_partial_ranking_functions_constraints(_Max,Head,Call,Phase,Chain,Top,Aux):-
		bagof_no_fail((Loops,Rf,Increment_deps,Unknown_deps_simple),
	Deps^Deps_type^Map_dependencies^Unknown_deps^Ignored^
	(
			partial_ranking_function(Head,Chain,Phase,Loops,Rf,Deps,Deps_type),
			maplist(tuple,Deps,Deps_type,Map_dependencies),			
			partition(increment_dep,Map_dependencies,Increment_deps,Unknown_deps),
			maplist(tuple,Unknown_deps_simple,Ignored,Unknown_deps)
		
			),Rfs),
	%	ut_split_at_pos(Rfs,Max,Rfs_selected,_),	
	  foldl(get_constr_from_partial_function(Head,Call,Phase),Rfs,([],[]),(Top,Aux)).

increment_dep((_,N)):-number(N).

get_constr_from_partial_function(Head,Call,_Phase,(Loops,Rf,[],[]),(Top_accum,Aux),(Top,Aux)):-
	maplist(cstr_get_it_name,Loops,Bounded),
	get_difference_version(Head,Call,Rf,Rf_diff),
	maplist(cstr_generate_top_exp(Bounded),[Rf,Rf_diff],[Top1,Top2]),
	Top=[Top1,Top2|Top_accum],!.
	
get_constr_from_partial_function(Head,Call,Phase,(Loops,Rf,Incr_deps,Unknown_deps),(Top_accum,Aux_accum),(Top,Aux)):-
		  maplist(cstr_get_it_name,Loops,Bounded),
		  get_difference_version(Head,Call,Rf,Rf_diff),
		  maplist(get_increase_summands,Incr_deps,Summands,Index),
		  maplist(get_mult_summands(Head,Rf,Phase),Unknown_deps,Summands2,Index2,Extra_tops),!,
		  cstr_name_aux_var(Name_aux),
		  ut_flat_list([Index,Index2],Index_total),
		  append(Summands,Summands2,Summands_total),
		  Aux=[bound([(Name_aux,Var_aux)|Index_total],add([mult([Var_aux])|Summands_total]),Bounded)|Aux_accum],
		  maplist(cstr_generate_top_exp([Name_aux]),[Rf,Rf_diff],[Top1,Top2]),
		  ut_flat_list([Top1,Top2,Extra_tops,Top_accum],Top).
		  	
get_constr_from_partial_function(_Head,_Call,_Phase,_,(Top,Aux),(Top,Aux)).

		   
get_increase_summands((Loop,Constant),mult([Var_aux,Constant]),(It_name,Var_aux)):-
	cstr_get_it_name(Loop,It_name).	   

get_mult_summands(Head,Rf,Phase,Loop,mult([Var_loop,Var_aux]),[(It_name,Var_loop),(Name_aux,Var_aux)],Extra_top):-
	cstr_get_it_name(Loop,It_name),
	cstr_name_aux_var(Name_aux),
	find_reset(Loop,Rf,Head,Phase,Reset),
	cstr_generate_top_exp([Name_aux],Reset,Extra_top).
		   
		   
		   
% If Rf is reseted to a new value in an equation Dep, after Dep Rf will have a fixed value.
% We try to relate such value with the initial values of the variables at the beginning of the
% phase using phase_star


find_reset(Dep,Rf,Head,Phase,Reset):-	
	get_phase_star(Head,Call,Phase,Cs_star),
	loop_ph(Call,(Dep,_),Call2,Cs,_,_),
    nad_glb(Cs,Cs_star,Cs_total),
	Head=..[_|EVars],
	copy_term((Head,Rf),(Call2,Rf_instance)),
	max_min_linear_expression_all(Rf_instance,EVars,Cs_total,max,Rf_bounds),
	(member(Reset,Rf_bounds)->
		true
		;
		term_variables(Call,Call_vars),
		max_min_linear_expression_all(Rf_instance,Call_vars,Cs,max,Rf_bounds2),
		Rf_bounds2\=[],
		format(user_error,'Could not find a reset to ~p in loop ~p phase ~p~n but not undefined: ~p',[Rf,Dep,Phase,Rf_bounds2]),
		fail
		),!.
  
		   	   
get_difference_version(Head,Call,Rf,Rf_diff):-
	copy_term((Head,Rf),(Call,Rfp)),
	normalize_le(Rf-Rfp,Rf_diff).



add_phase_lower_bounds(Head,Call,Phase,Chain,Top,Aux):-
	rf_limit(Max),
	get_ranking_functions_lower_constraints(Max,Head,Call,Phase,Chain,Top,Aux).
	%get_partial_ranking_functions_constraints(Max,Head,Call,Phase,Chain,Top2,Aux2),
	%append(Top1,Top2,Top),
	%append(Aux1,Aux2,Aux).
	
get_ranking_functions_lower_constraints(Max,Head,Call,Phase,Chain,Top,[]):-
		bagof_no_fail(Df,
			get_lower_bound_val(Head,Call,Chain,Phase,Df)
	   ,Dfs),
	   ut_split_at_pos(Dfs,Max,Dfs_selected,_),
	   maplist(cstr_get_it_name,Phase,Bounded),
	   maplist(cstr_generate_top_exp(Bounded),Dfs_selected,Top).
	   
get_lower_bound_val(Head,Call,Chain,Phase,LB):-
	ranking_function(Head,Chain,Phase,Rf),
	copy_term((Head,Rf),(Call,Rf1)),
	phase_loop(Phase,_,Head,Call,Phi),
	normalize_constraint( D=Rf-Rf1 ,Constraint),
	Cs_1 = [ Constraint | Phi],
	nad_maximize(Cs_1,[D],[Delta1]),
	normalize_le(1/Delta1*(Rf-Rf1),LB).

/*	
get_lower_bound_val(Head,Call,Chain,Phase,Val):-
	partial_ranking_function(Head,Chain,Phase,_,Rf,_,_),
	copy_term((Head,Rf),(Call,Rf1)),
	normalize_constraint( D=Rf-Rf1 ,Constraint),
	maplist(get_maximum_decrease(Head,Call,(D,Constraint)),Phase,Modifications),
	exclude(zero_modification,Modifications,Non_zero_modifications),
	partition(positive_modification,Non_zero_modifications,Positive,Non_positive),
	partition(negative_modification,Non_positive,Negative,Unknown),
	length(Non_positive,N),
	%for now, do not allow resets
	Unknown=[],
	maplist(tuple,Loops,Nums,Positive),
	max_list(Nums,Max),
	normalize_le(1/Max*(Rf-Rf1),LB),
	Val= N-val(Loops,LB,Negative,[],0).
*/	
get_maximum_decrease(Head,Call,(D,Constraint),Loop,(Loop,Delta)):-
	loop_ph(Head,(Loop,_),Call,Cs,_,_),
	Cs_1 = [ Constraint | Cs],
	nad_maximize(Cs_1,[D],[Delta]),!.
	
get_maximum_decrease(_,_,_,Loop,(Loop,unknown)).
	
zero_modification((_,N)):-number(N),N =:= 0.
zero_modification((_,N/D)):-number(N),number(D),N =:= 0.

positive_modification((_,N)):-number(N),N > 0.
positive_modification((_,N/D)):-number(N),number(D),N > 0,D > 0.

negative_modification((_,N)):-number(N),N < 0.
negative_modification((_,N/D)):-number(N),number(D),N < 0,D > 0.

/*

%FIXME: basic treatment
add_phase_lower_bounds(Head,Call,Phase,_Chain,It_vars,[],Abstract_norms):-!,
	maplist(tuple,Phase,It_vars,It_var_dictionary),
	%rf_limit establishes how many bounds we want to generate per loop
	rf_limit(Max),
	length(Phase,N_loops),
	repeat_n_times(N_loops,Max,Counters),
	maplist(tuple,Phase,Counters,Phase_counters),
	% collect all the ranking functions and their dependencies
	% sort them according to the number of dependencies
	obtain_initial_inverse_rf_stucture(Head,Call,Chain,Phase,Structure),
	% incrementally find upper bounds for each of the phases until the counters reach 0,
    % the available ranking functions are all consumed or
    % we find a ranking function with unresolved dependencies
	find_phase_bounds(Structure,min,Phase_counters,(Head,Phase,Chain),[],Concrete_norms),
	%substitute the cost_equation_id of the phase by the corresponding iteration variables
	maplist(abstract_norms(It_var_dictionary),Concrete_norms,Abstract_norms).


	
%! obtain_initial_inverse_rf_stucture(Head:term,Call:term,Chain:chain,Phase:phase,Structure:rf_structure) is det
% get all the ranking functions of the phase Phase in the chain Chain.
% create a data structure Structure.
%
% rf_structure:list(int-val(list(equation_id),linear_expression,list((equation_id,int)),list(equation_id),cost_expression))
% This data structure is a sorted list
% of ranking functions that are sorted by the number of dependencies they have.
% each element contains the specific dependencies in two categories: the Increment_deps
% and the Unknown_deps. The equations in Increment_deps increment the ranking function by a
%constant, the Unkown_deps reset the value of the ranking function.
% Finally, the last part of the ranking function contains the additional expression
% that has to be added to the rf to account for dependencies that have been already removed
obtain_initial_inverse_rf_stucture(Head,Call,Chain,Phase,Structure):-
	bagof_no_fail(Val,
		get_lower_bound_val(Head,Call,Chain,Phase,Val)
		,Deps_structure),
	%order ranking function by number of dependencies
	keysort(Deps_structure,Structure).
	



*/