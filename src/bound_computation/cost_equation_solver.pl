/** <module> cost_equation_solver

This module computes the cost structure of one application of a cost equation in terms of 
the input variables and the variables of the recursive call (if there is one)

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


:- module(cost_equation_solver,[
	compute_ce_bounds/3,
	compute_loop_bounds/3]).

:- use_module(constraints_maximization,[
	max_min_fconstrs_in_cost_equation/6,
	max_min_linear_expression_all/5]).
	
:- use_module('../IO/params',[get_param/2]).
:- use_module('../IO/output',[
	print_warning_in_error_stream/2,
	print_header/3]).

:- use_module('../utils/crs',[
	ce_rec_calls/2,
	ce_get_cost/2,
	ce_set_cost/3,
	ce_head/2,
	ce_set_cost/3,	
		
	cr_apply_all_ce_with_id/3,
	cr_get_ce_by_id_fresh/3,
	cr_IOvars/2,
	cr_get_external_patterns/2,
	
	crs_get_cr/3
	]).
:- use_module('../refinement/loops',[
	loop_calls/2,
	loop_head/2,
	loop_get_CEs/2,
	loops_apply_to_each_loop/3,
	loop_set_cost/3
	]).	
:- use_module('../refinement/unfolding',[
   external_patterns_head/2,
   external_patterns_get_external_pattern/3,
   external_pattern_cost/2
   ]).		

:- use_module('../utils/cofloco_utils',[ground_copy/2]).
:- use_module('../utils/cost_structures',[
	cstr_extend_variables_names/3,
	cstr_empty/1,
	cstr_simplify/2,
	cstr_or_compress/2,
	max_min_ub_lb/2,
	bconstr_accum_bounded_set/3]).


:- use_module(stdlib(fraction),[sum_fr/3]).
:- use_module(stdlib(linear_expression),[write_le/2]).
:- use_module(stdlib(utils),[ut_flat_list/2]).
:- use_module(stdlib(set_list)).


:-use_module(library(apply_macros)).
:-use_module(library(lists)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
compute_loop_bounds(Loops,CR,Loops2):-
	loops_apply_to_each_loop(cost_equation_solver:get_loop_cost(CR),Loops,Loops2).

get_loop_cost(CR,Loop,Loop2):-
	loop_get_CEs(Loop,Eqs),
	loop_head(Loop,Head),
	loop_calls(Loop,Calls),
    maplist(cr_get_ce_cost(CR,Head,Calls),Eqs,Costs),
    cstr_or_compress(Costs,Final_cost),
    loop_set_cost(Loop,Final_cost,Loop2).
    
cr_get_ce_cost(CR,Head,Calls,CE_id,Cost):-
	cr_get_ce_by_id_fresh(CR,CE_id,CE),
	%unify the corresponing variables
	ce_head(CE,Head),
	ce_rec_calls(CE,Calls),
	ce_get_cost(CE,Cost).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	
compute_ce_bounds(CR,CRS,CR2):-
	cr_IOvars(CR,IOvars),
	cr_apply_all_ce_with_id(cost_equation_solver:get_equation_cost(CRS,IOvars),CR,CR2).

get_equation_cost(CRS,IOvars,(Id,Eq),(Id,Eq2)):-
		Eq=eq_ref(Head,Basic_cost, Base_calls,Rec_Calls,_,Cs,_),

		foldl(accumulate_calls(Id,CRS),Base_calls,(Basic_cost,1),(cost(Ub_fconstrs_list,Lb_fconstrs_list,Iconstrs,Bases,Base),_)),
		% we reverse the calls in case we want to combine cost structures incrementally
		% this is not done now but it would allow us to detect which calls make us lose precision
		%reverse(Base_calls,Base_calls_inv),
		max_min_fconstrs_in_cost_equation(Ub_fconstrs_list,Base_calls,Cs,(Head,Rec_Calls,IOvars),New_Ub_fconstrs,New_iconstrs1),
		%for finding interesting examples
		%get_lost_fconstrs_expressable_as_outputs(Id,Ub_fconstrs_list,New_Ub_fconstrs,Base_calls,Phi),
		max_min_fconstrs_in_cost_equation(Lb_fconstrs_list,Base_calls,Cs,(Head,Rec_Calls,IOvars),New_Lb_fconstrs,New_iconstrs2),
		ut_flat_list([New_iconstrs1,New_iconstrs2,Iconstrs],New_iconstrs),
	
		(get_param(debug,[])->print_header('Simplifying cost structure of CE ~p ~n',[Id],4);true),
		Cost_complex=cost(New_Ub_fconstrs,New_Lb_fconstrs,New_iconstrs,Bases,Base),
		cstr_simplify(Cost_complex,Cost),
		
		ce_set_cost(Eq,Cost,Eq2).

	
accumulate_calls(Eq_id,CRS,Pattern:Call,(cost(Ub_fconsts1,Lb_fconsts1,Iconstrs1,Bases1,Base1),N),(cost([Ub_fconsts2|Ub_fconsts1],[Lb_fconsts2|Lb_fconsts1],[Iconstrs2|Iconstrs1],Bases,Base),N1)) :-
    N1 is N+1,
    
    functor(Call,Name_call,_),
    crs_get_cr(CRS,Name_call,CR),
    cr_get_external_patterns(CR,External_patterns),
    copy_term(External_patterns,External_patterns_fresh),
    external_patterns_head(External_patterns_fresh,Call),
    external_patterns_get_external_pattern(External_patterns_fresh,Pattern,External_pattern),
    external_pattern_cost(External_pattern,Cost_call),
    
    % we extend the names of the intermediate variables to ensure they are unique
    cstr_extend_variables_names(Cost_call,eq(Eq_id,N),cost(Ub_fconsts2,Lb_fconsts2,Iconstrs2,Bases2,Base2)),
    sum_fr(Base1,Base2,Base),
    append(Bases2,Bases1,Bases).


    
/*


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% predicates for finding interesting examples

get_lost_fconstrs_expressable_as_outputs(Eq_id,Fconstrs_list,Final_fconstrs,Base_calls,Phi):-
	get_param(debug,[]),!,
	ut_flat_list(Fconstrs_list,Fconstrs),
	reverse(Base_calls,Base_calls_rev),
	foldl(bconstr_accum_bounded_set,Fconstrs,[],Itvar_set),
	foldl(exclude_covered_itvars,Final_fconstrs,Itvar_set,Lost_itvar_set),
	get_lost_fconstrs_expressable_as_outputs_1(Fconstrs_list,Base_calls_rev,Phi,Eq_id,Lost_itvar_set).

get_lost_fconstrs_expressable_as_outputs(_,_,_,_,_).

get_lost_fconstrs_expressable_as_outputs_1(_,[],_,_,_):-!.

get_lost_fconstrs_expressable_as_outputs_1([Fconstrs|Fconstr_list],[_Call|Base_calls],Phi,Eq_id,Lost_itvar_set):-
	include(constr_bounded_in_set(Lost_itvar_set),Fconstrs,Fconstrs_lost),
	foldl(get_call_output_vars,Base_calls,[],Out_vars),
	get_fconstrs_expressable_with_vars(Fconstrs_lost,Out_vars,Phi,Recoverable_exps),
	(Recoverable_exps\=[]->
		term_variables(Recoverable_exps,Important_vars),
		from_list_sl(Important_vars,Important_vars_set),
		include(term_contains_vars(Important_vars_set),Base_calls,Important_calls),
		ground_copy((Important_calls,Recoverable_exps),(Important_calls2,Recoverable_exps2)),
		maplist(write_le,Recoverable_exps2,Recoverable_exps_print),
		print_warning_in_error_stream('Expressions ~p lost in CE ~p in terms of the output ~p~n',[Recoverable_exps_print,Eq_id,Important_calls2])
		;
		true),
	get_lost_fconstrs_expressable_as_outputs_1(Fconstr_list,Base_calls,Phi,Eq_id,Lost_itvar_set).
	
term_contains_vars(Set,Term):-
	term_variables(Term,Vars),
	from_list_sl(Vars,Vars_set),
	intersection_sl(Set,Vars_set,[_|_]),!.

exclude_covered_itvars(bound(_,_,Bounded),Set,Set1):-
	from_list_sl(Bounded,Bounded_set),
	difference_sl(Set,Bounded_set,Set1).
	
constr_bounded_in_set(Set,bound(_,_,Bounded)):-
	from_list_sl(Bounded,Bounded_set),
	difference_sl(Bounded_set,Set,[]).

get_call_output_vars((Call,_Chain),OVars,OVars2):-
	get_input_output_vars(Call,_,OVars1),
	append(OVars1,OVars,OVars2).
	
get_fconstrs_expressable_with_vars([],_,_,[]).
get_fconstrs_expressable_with_vars([bound(Op,Lin_exp,_Bounded)|Fconstrs],Out_vars,Phi,[Lin_exp2|Lin_exps]):-
	max_min_ub_lb(Max_min,Op),
	max_min_linear_expression_all(Lin_exp, Out_vars, Phi,Max_min, [Lin_exp2|_]),!,
	get_fconstrs_expressable_with_vars(Fconstrs,Out_vars,Phi,Lin_exps).
	
get_fconstrs_expressable_with_vars([_|Fconstrs],Out_vars,Phi,Lin_exps):-
	get_fconstrs_expressable_with_vars(Fconstrs,Out_vars,Phi,Lin_exps).

*/

