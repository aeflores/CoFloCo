/** <module> phase_max_min_strategy

This module implements the triangular_strategy.
This strategy obtain the sum of a linear expression in the phase for cases where the linear expression is
incremented/decremented by a constant value in each iteration.

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


:- module(phase_triangular_strategy,[
		triangular_strategy/8
	]).
	
:- use_module(phase_common).
:- use_module(phase_inductive_sum_strategy,[find_minsum_constraint/8]).
:- use_module(phase_solver,[			
				enriched_loop/4,
		        save_pending_list/6]).
:- use_module('../../db',[get_input_output_vars/3]).			        
:- use_module('../constraints_maximization',[max_min_linear_expression_all/5]).		
:- use_module('../../IO/params',[get_param/2]).		
:- use_module('../../utils/cost_structures',[
			new_itvar/1,
			get_loop_itvar/2,
			astrexp_new/2,
			fconstr_new/4,
			iconstr_new/4]).			
:- use_module(stdlib(numeric_abstract_domains),[nad_maximize/3,nad_entails/3]).
:- use_module(stdlib(linear_expression),[negate_le/2]).				
:- use_module(stdlib(fraction),[greater_fr/2,multiply_fr/3]).
:- use_module(stdlib(fraction_list),[max_frl/2]).
:- use_module(stdlib(utils),[ut_flat_list/2]).
:- use_module(library(apply_macros)).
:- use_module(library(lists)).	
	
%triangular strategy
% valid for minsums of expressions that are not constant	

triangular_strategy(bound(lb,Lin_exp,Bounded_ini),loop_vars(Head,[Call]),Loop,Phase,New_fconstrs,New_iconstrs,Pending,Pending_out):-	
	Lin_exp\=[]+_,
	enriched_loop(Loop,Head,[Call],Cs),
	%obtain an expressions only in terms of the initial variables of the loop
	(is_head_expression(Head,Lin_exp)->
		Exp=Lin_exp
	;
	 get_input_output_vars(Head,Input_vars_head,_),
	 max_min_linear_expression_all(Lin_exp, Input_vars_head, Cs,min, Mins),
	 member(Exp,Mins)
	),
	%the cost is increased or decreased by a constant
	get_difference_version(Head,Call,Exp,Exp_diff),	
	le_print_int(Exp_diff,Exp_diff_int,Exp_diff_denominator),
	nad_maximize([Exp_diff_int=Exp_diff_denominator*D|Cs],[D],[Delta]),
	%a flag that indicates whether the cost increases or decreases
	(
	(greater_fr(Delta,0),Dir=pos)
	;
	(greater_fr(0,Delta),Dir=neg)
	),	
	%check the effect of other loops, 
	delete(Phase,Loop,Phase_rest),
	check_loops_triangle_minsum(Phase_rest,Dir,Head,Call,Pending,Exp,Included_loops,Bounded,Increments,Pending_out),
	append(Bounded_ini,Bounded,Bounded_vars),
	% generate an intermediate constraint that is the sum of all the iterations of the Included_loops
	get_it_sum_aux([Loop|Included_loops],Aux_all_iter_iconstr,All_iterations_name),
	%obtain the minimum initial value of the expression taking the Other_loops into account
	new_itvar(Initial_name),
	fconstr_new([Initial_name],lb,Exp,FConstr_ini),
	max_frl([Delta|Increments],Min_increment),
	%depending on whether we increment or decrement
	(Dir=pos->
		multiply_fr(Min_increment,1/2,Min_increment_scaled),
		New_fconstrs2=[],
	    % we substract the decrements
	    astrexp_new(add([mult([All_iterations_name,Initial_name]),mult([All_iterations_name,Min_increment_scaled])])-add([mult([All_iterations_name,All_iterations_name,Min_increment_scaled])]),Astrexp)
	;
		multiply_fr(Min_increment,-1/2,Min_increment_scaled),
		negate_le(Exp,Exp_neg),
		new_itvar(Initial_name_neg),
		fconstr_new([Initial_name_neg],ub,Exp_neg,FConstr_ini2),
		New_fconstrs2=[FConstr_ini2],
		%we add the increments, but we substract the negation of the initial value in case this one is negative	
		astrexp_new(add([mult([All_iterations_name,Initial_name]),mult([All_iterations_name,All_iterations_name,Min_increment_scaled])])-add([mult([Initial_name_neg,All_iterations_name]),mult([All_iterations_name,Min_increment_scaled])]),Astrexp)
	),
	iconstr_new(Astrexp,lb,Bounded_vars,Main_iconstr),
	ut_flat_list([[FConstr_ini],New_fconstrs2],New_fconstrs),!,
	ut_flat_list([Aux_all_iter_iconstr,Main_iconstr],New_iconstrs),!.
	
	
	
	
	%! get_it_sum_aux(+Involved_loops:list(loop_id),-Iconstrs:list(iconstr),-All_iterations_var:itvar) is det
% create new intermediate variable All_iterations_var and two intermediate constraints Iconstrs that
% bound it to the sum of number of iterations of Involved_loops
get_it_sum_aux(Involved_loops,Iconstrs,All_iterations_var):-
	maplist(get_loop_itvar,Involved_loops,Involved_it_vars),
	maplist(put_inside_mult,Involved_it_vars,It_summands),
	astrexp_new(add(It_summands)-add([]),Astrexp),
	new_itvar(All_iterations_var),	
	copy_term(Astrexp,Astrexp2),
	iconstr_new(Astrexp,lb,[All_iterations_var],Lb_iconstr),
	iconstr_new(Astrexp2,ub,[All_iterations_var],Ub_iconstr),
	Iconstrs=[Lb_iconstr,Ub_iconstr].
	
	
	
	%! check_loops_triangle_minsum(Loops:loop_id,Pos_neg:flag,Head:term,Call:term,Pending:pending_constrs,Exp:nlinexp,Included_loops:list(loop_id),Bounded:list(itvar),Increments:list(rational),Other_loops:list(loop_id),Pending_out:pending_constr) is det
% examine the behavior of Loops with respecto to Exp
% * Included_loops are a list of  loops that are included
% * Bounded are a list of itvars that are bounded by the expression Exp
% * Increments is list of how much Exp is incremented or decremented in the included loops
% * Other_loops list of loops that are not included
% For each included loop we remove a pending constraint, Pending_sum is the resulting pending constraints
%
% We include loops that increment or decrement Exp by a constant and contain a pending constraint bounded by Exp
% we put the rest of the loops in Other_loops
check_loops_triangle_minsum([],_Pos_neg,_Head,_Call,Pending,_Exp,[],[],[],Pending).
check_loops_triangle_minsum([Loop|Loops],Pos_neg,Head,Call,Pending,Exp,[Loop|Included_loops],Bounded_total,[Increment|Increments],Pending_out):-
	check_loop_triangle_minsum(Loop,Pos_neg,Head,Call,Pending,Exp,Bounded,Increment,Pending_aux),!,
	check_loops_triangle_minsum(Loops,Pos_neg,Head,Call,Pending_aux,Exp,Included_loops,Bounded_aux,Increments,Pending_out),
	append(Bounded,Bounded_aux,Bounded_total).

check_loops_triangle_minsum([Loop|Loops],Pos_neg,Head,Call,Pending,Exp,[Loop|Included_loops],Bounded,Increments,Pending_out):-
	check_loop_triangle_no_change(Loop,Head,Call,Exp),!,
	check_loops_triangle_minsum(Loops,Pos_neg,Head,Call,Pending,Exp,Included_loops,Bounded,Increments,Pending_out).

	
check_loop_triangle_minsum(Loop,Pos_neg,Head,Call,Pending,Exp,Bounded,Delta,Pending1):-	
	enriched_loop(Loop,Head,[Call],Cs),
	get_difference_version(Head,Call,Exp,Exp_diff),	
	le_print_int(Exp_diff,Exp_diff_int,Exp_diff_denominator),
	nad_maximize([Exp_diff_int=Exp_diff_denominator*D|Cs],[D],[Delta]),
	(Pos_neg=pos->
		greater_fr(Delta,0)
	;
		greater_fr(0,Delta)
	),
	find_minsum_constraint(Loop,Head,[Call],Cs,Exp,Bounded,Pending,Pending1),!,
	(get_param(debug,[])->format('Loop ~p is triangle collaborative with ~p ~n',[Loop,Delta]);true).

check_loop_triangle_no_change(Loop,Head,Call,Exp):-	
	enriched_loop(Loop,Head,[Call],Cs),
	term_variables((Head,Call),Vars),	
	get_difference_version(Head,Call,Exp,Exp_diff),	
	le_print_int(Exp_diff,Exp_diff_int,_Exp_diff_denominator),
	nad_entails(Vars,Cs,[Exp_diff_int=0]).
	