/** <module> constraints_generation

This module generates new constraints for the iteration variables of a phase based on 
the ranking functions.


Specific "data types" of this module:
  * rf_structure:list(int-val(list(equation_id),linear_expression,list((equation_id,int)),list(equation_id),cost_expression))
    This data structure is a sorted list
    of ranking functions that are sorted by the number of dependencies they have.
    each element contains the specific dependencies in two categories: the Increment_deps
    and the Unknown_deps. The equations in Increment_deps increment the ranking function by a
    constant, the Unkown_deps reset the value of the ranking function.
    Finally, the last part of the ranking function contains the additional expression
    that has to be added to the rf to account for dependencies that have been already removed
    
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
		add_phase_upper_bounds/8,
		add_phase_lower_bounds/7
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
:- use_module('../utils/cost_structures',[remove_it_vars_from_constr/3]).					      

:- use_module(stdlib(utils),[ut_flat_list/2]).
:- use_module(stdlib(set_list)).
:- use_module(stdlib(list_map),[lookup_lm/3]).
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

%! add_phase_upper_bounds(Head:term,Call:term,Phase:phase,Chain:chain,It_vars:list(var),Removed_vars:list_set(var),Abstract_norms2:list(norm),Differential_norms:list(norm)) is det
% given a Phase in a Chain generate 2 sets of norms that bound the number of iterations
% of each component of the Phase. 
%  * Abstract_norms2 depend on the initial variables of the phase (the ones of Head)
%  * Differential_norms depend on both the initial and the final variables of the phase (Head and Call)
%
% the iteration variables in Removed vars are excluded form the generated norms.
% It_vars contains the concrete variables that correspond to each of the loops of Phase.
add_phase_upper_bounds(Head,Call,Phase,Chain,It_vars,Removed_vars,Abstract_norms2,Differential_norms):-
	maplist(tuple,Phase,It_vars,It_var_dictionary),
	%rf_limit establishes how many bounds we want to generate per loop
	rf_limit(Max),
	length(Phase,N_loops),
	repeat_n_times(N_loops,Max,Counters),
	maplist(tuple,Phase,Counters,Phase_counters),
	% collect all the ranking functions and their dependencies
	% sort them according to the number of dependencies
	obtain_initial_rf_stucture(Head,Chain,Phase,Structure),
    % incrementally find upper bounds for each of the phases until the counters reach 0,
    % the available ranking functions are all consumed or
    % we find a ranking function with unresolved dependencies
	find_phase_bounds(Structure,max,Phase_counters,(Head,Phase,Chain),[],Concrete_norms),
	%substitute the cost_equation_id of the phase by the corresponding iteration variables
	maplist(abstract_norms(It_var_dictionary),Concrete_norms,Abstract_norms),
	% remove the iteration variables of Removed_vars
	maplist(remove_it_vars_from_constr(Removed_vars),Abstract_norms,Abstract_norms1),
	exclude(empty_norm,Abstract_norms1,Abstract_norms2),
	%generate new norms by taking the difference between the norm in terms of Head 
	% and the norm in terms of Call
	get_differential_norms(Abstract_norms2,Head,Call,Differential_norms).

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

	
%! abstract_norms(+Dictionary:list_map(equation_id,var),+Norm_concrete:norm,-Norm_abstract:norm) is det
% substitute the "iteration variables" of Norm_concrete that are equation_ids
% by the corresponding real iteration variables
abstract_norms(Dictionary,norm(Its,Exp),norm(Its3,Exp)):-
	maplist(lookup_lm(Dictionary),Its,Its2),
	from_list_sl(Its2,Its3).

empty_norm(norm([],_)).
	
%! 	get_differential_norms(+Norms:list(norm),+Head:term,+Call:term,-Norms_out:list(norm)) is det
% for every norm that is a linear expression, we create a new norm that
% is the difference between the initial value and the final value of the norm.
% That is, the norm expressed in terms of Head and Call.
get_differential_norms([],_Head,_Call,[]).
get_differential_norms([norm(Its,Exp)|Norms],Head,Call,[norm(Its,Exp_diff)|Norms_out]):-
	is_linear_exp(Exp),!,
	copy_term((Head,Exp),(Call,Exp_2)),
	cexpr_simplify_ctx_free(Exp-Exp_2,Exp_diff),
	get_differential_norms(Norms,Head,Call,Norms_out).
	
get_differential_norms([norm(_Its,_Exp)|Norms],Head,Call,Norms_out):-
	get_differential_norms(Norms,Head,Call,Norms_out).	
	

%! obtain_initial_rf_stucture(Head:term,Chain:chain,Phase:phase,Structure:rf_structure) is det
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
obtain_initial_rf_stucture(Head,Chain,Phase,Structure):-
	bagof_no_fail(0-val(Phase,Rf,[],[],0),
	ranking_function(Head,Chain,Phase,Rf)
	   ,Rfs),
	bagof_no_fail(NDeps-val(Loops,Rf,Increment_deps,Unknown_deps_simple,0),
	Deps^Deps_type^Map_dependencies^Unknown_deps^Ignored^
	(
			partial_ranking_function(Head,Chain,Phase,Loops,Rf,Deps,Deps_type),
			maplist(tuple,Deps,Deps_type,Map_dependencies),			
			length(Map_dependencies,NDeps),
			partition(increment_dep,Map_dependencies,Increment_deps,Unknown_deps),
			maplist(tuple,Unknown_deps_simple,Ignored,Unknown_deps)
		
			),Deps_structure),
	%order ranking function by number of dependencies
	keysort(Deps_structure,Sorted_structure),
	append(Rfs,Sorted_structure,Structure).

increment_dep((_,N)):-number(N).	


	
%! find_phase_upper_bounds(+Structure:rf_structure,+Counters:list_map(equation_id,int),+Phase_info:(term,phase,chain),+Norms_accum:list(norm),-Concrete_norms:list(norm))	is det
% visit the rf_structure until all the needed norms have been obtained (Counters=[]);
% the structure is empty (Structure=[]) or there are no more elements without dependencies.
%
% For each element without dependencies, create a new norm, decrease the counters
% of the involved cost equations and  (try to) remove the elements where that element appears as
% a dependency


find_phase_bounds(_Structure,_,[],_Phase_info,Concrete_norms,Concrete_norms):-!.
find_phase_bounds([],_,_,_Phase_info,Concrete_norms,Concrete_norms):-!.
find_phase_bounds([0-val(Loops,Rf,[],[],Accum)|Deps],Max_Min,Counters,Phase_info,Norms_accum,Norms):-!,
    update_ub_counters(Counters,Loops,Counters2),
    Norms_accum2=[norm(Loops,Rf+Accum)|Norms_accum],
	update_deps_ub_structure(Deps,Max_Min,Loops,Rf+Accum,Phase_info,Deps1),
	find_phase_bounds(Deps1,Max_Min,Counters2,Phase_info,Norms_accum2,Norms).
find_phase_bounds([N-val(Loop,Rf,Incr_Deps,Unknown_Deps,Accum)|Deps],Max_Min,Counters,Phase_info,Norms_accum,Norms):-
	N>0,
	keysort([N-val(Loop,Rf,Incr_Deps,Unknown_Deps,Accum)|Deps],[N2-val(Loop2,Rf2,Incr_Deps2,Unknown_Deps2,Accum2)|Deps2]),
	(N2=0->
	 find_phase_bounds([N2-val(Loop2,Rf2,Incr_Deps2,Unknown_Deps2,Accum2)|Deps2],Max_Min,Counters,Phase_info,Norms_accum,Norms)
	;
	 Norms=Norms_accum
	).

%! update_ub_counters(+Counters:list_map(equation_id,int),+Loops:set_list(equation_id),-Counters2:list_map(equation_id,int)) is det
% remove one from the counters corresponding to the cost equations in Loops
% if a counter reaches 0, remove the pair from the map
update_ub_counters([],_,[]).
update_ub_counters(Counters,[],Counters):-!.
update_ub_counters([(Loop,N)|Cnts],[Loop|Loops],Counters):-!,
	N1 is N-1,
	(N1 > 0-> 
	   Counters=[(Loop,N1)|Counters_aux]
	   ;
	   Counters=Counters_aux
	   ),
	update_ub_counters(Cnts,Loops,Counters_aux).
update_ub_counters([(Loop,N)|Cnts],[Loop2|Loops],[(Loop,N)|Counters_aux]):-
	Loop < Loop2,!,
	update_ub_counters(Cnts,[Loop2|Loops],Counters_aux).	
	
update_ub_counters([(Loop,N)|Cnts],[Loop2|Loops],Counters_aux):-
	Loop > Loop2,
	update_ub_counters([(Loop,N)|Cnts],Loops,Counters_aux).		


%! update_deps_ub_structure(+Structure:rf_structure,+Loops_ub:set_list(equation_id),+Ub:cost_expression,+Phase_info:(term,phase,chain),-Structure_out:rf_structure) is det
% For each element in Structure:
%
% * Remove the increment dependencies to the loops in Loops_ub, obtain the maximum increment Max_incr
%   and add Max_inc* Ub to the accumulator
% * For the loops In Loops_ub that are unknown dependencies, 
%   try to find a reset value of the ranking function in that loop.
%   * If no reset is found, the dependency is not removed
%   * If we find a reset, we add max(Resets)* nat(Ub) to the accumulator
% * Finally, we recompute the number of dependencies
update_deps_ub_structure([],_,_,_,_,[]).

%if the loops are already bounded by the removed ranking, we don't wanna accumulate this value on top
update_deps_ub_structure([N-val(Loops,Rf,Incr_Deps,Unknown_Deps,Accum)|Deps],Max_Min,Loops_ub,Ub,Phase_info,
                         [N-val(Loops,Rf,Incr_Deps,Unknown_Deps,Accum)|Desp1]):-
	 difference_sl(Loops,Loops_ub,[]),!,                        
	update_deps_ub_structure(Deps,Max_Min,Loops_ub,Ub,Phase_info,Desp1).

update_deps_ub_structure([_-val(Loops,Rf,Incr_Deps,Unknown_Deps,Accum)|Deps],Max_Min,Loops_ub,Ub,Phase_info,
                         [N2-val(Loops,Rf,Incr_Deps2,Unknown_Deps2,Accum2)|Desp1]):-
	(remove_incr_loops(Incr_Deps,Max_Min,Loops_ub,Incr_Deps2,Incr)->
	(Incr >0 -> 
	      %Accum1=Accum+Incr* nat(Ub)
	      Accum1=Accum+Incr* Ub
	      ;
	      Accum1=Accum
	 )
	 ;
	 %it fails for the lower bounds if it does not depend on the complete Loops_ub
	 Incr_Deps2=Incr_Deps,
	 Accum1=Accum
	 ),
	intersection_sl(Unknown_Deps,Loops_ub,Removable_Unknown_deps),
	find_resets(Removable_Unknown_deps,Rf,Phase_info,Removed_deps,Resets),
	(Resets\=[]->
	   Accum2=Accum1+max(Resets)* nat(Ub)
	   ;
	   Accum2=Accum1
	   ),
	difference_sl(Unknown_Deps,Removed_deps,Unknown_Deps2),
	
	length(Incr_Deps2,N2_1),
	length(Unknown_Deps2,N2_2),
	N2 is N2_1+N2_2,
	update_deps_ub_structure(Deps,Max_Min,Loops_ub,Ub,Phase_info,Desp1).



remove_incr_loops([],max,_Loops_ub,[],0).
remove_incr_loops([(Loop,N)|Incr_Deps],max,Loops_ub,Incr_Deps2,Max_incr):-
	contains_sl(Loops_ub,Loop),!,
	remove_incr_loops(Incr_Deps,max,Loops_ub,Incr_Deps2,Max_incr_aux),
	Max_incr is max(Max_incr_aux,N).


remove_incr_loops(_,min,[],[],inf).	
remove_incr_loops([(Loop,N)|Incr_Deps],min,Loops_ub,Incr_Deps2,Min_incr):-
	contains_sl(Loops_ub,Loop),!,
	remove_sl(Loops_ub,Loop,Loops_ub1),
	remove_incr_loops(Incr_Deps,min,Loops_ub1,Incr_Deps2,Min_incr_aux),
	NNeg is 0-N,
	(Min_incr_aux=inf->
	  Min_incr=NNeg
	  ;
	  Min_incr is min(Min_incr_aux,NNeg)
	).

remove_incr_loops([(Loop,N)|Incr_Deps],Max_Min,Loops_ub,[(Loop,N)|Incr_Deps2],Incr):-
	remove_incr_loops(Incr_Deps,Max_Min,Loops_ub,Incr_Deps2,Incr).
	
% If Rf is reseted to a new value in an equation Dep, after Dep Rf will have a fixed value.
% We try to relate such value with the initial values of the variables at the beginning of the
% phase using phase_star

find_resets([],_,_Phase_info,[],[]).

find_resets([Dep|Deps],Rf,(Head,Phase,Chain),[Dep|Removed_deps],[Reset|Resets]):-	
	get_phase_star(Head,Call,Phase,Cs_star),
	loop_ph(Call,(Dep,_),Call2,Cs,_,_),
    nad_glb(Cs,Cs_star,Cs_total),
	Head=..[_|EVars],
	copy_term((Head,Rf),(Call2,Rf_instance)),
	max_min_linear_expression_all(Rf_instance,EVars,Cs_total,max,Rf_bounds),
	member(Reset,Rf_bounds),!,
	find_resets(Deps,Rf,(Head,Phase,Chain),Removed_deps,Resets).
	
find_resets([_Dep|Deps],Rf,Phase_info,Removed_deps,Resets):-	
	find_resets(Deps,Rf,Phase_info,Removed_deps,Resets).	
	
	
	
	
	
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
	


get_lower_bound_val(Head,Call,Chain,Phase,Val):-
	ranking_function(Head,Chain,Phase,Rf),
	copy_term((Head,Rf),(Call,Rf1)),
	phase_loop(Phase,_,Head,Call,Phi),
	normalize_constraint( D=Rf-Rf1 ,Constraint),
	Cs_1 = [ Constraint | Phi],
	nad_maximize(Cs_1,[D],[Delta1]),
	normalize_le(1/Delta1*(Rf-Rf1),LB),
	Val= 0-val(Phase,LB,[],[],0).
	
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
	
get_maximum_decrease(Head,Call,(D,Constraint),Loop,(Loop,Deltanum)):-
	loop_ph(Head,(Loop,_),Call,Cs,_,_),
	Cs_1 = [ Constraint | Cs],
	nad_maximize(Cs_1,[D],[Delta]),
	Deltanum is Delta,
	!.
	
get_maximum_decrease(_,_,_,Loop,(Loop,unknown)).
	
zero_modification((_,N)):-number(N),N =:= 0.
positive_modification((_,N)):-number(N),N > 0.
negative_modification((_,N)):-number(N),N < 0.