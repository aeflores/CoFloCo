/** <module> phase_max_min_strategy

This module implements the max_min_strategy. This strategy obtains the maximum or minimum value
of a linear expression in a phase. It does so by checking whether the expression is incremented,
decremented or reset.
The constraint generated is:

For the maximum case: the maximum of all the resets and the expression plus the sum of all the increments
For the minimim case: the minimum of all the resets and the expression minus the sum of all the decrements

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
:- module(phase_max_min_strategy,[
		max_min_strategy/7
	]).
	
:- use_module(phase_common).
:- use_module(phase_solver,[				
				enriched_loop/4,
		        save_pending_list/6]).
		        
:- use_module('../../db',[get_input_output_vars/3]).			        
:- use_module('../constraints_maximization',[max_min_linear_expression_all/5]).		
:- use_module('../../IO/params',[get_param/2]).					
:- use_module('../../utils/cofloco_utils',[ground_copy/2]).	
:- use_module('../../utils/cost_structures',[
			new_itvar/1,
			get_loop_itvar/2,
			astrexp_new/2,
			pstrexp_pair_empty/1,
			pstrexp_pair_add/3,
			fconstr_new/4,
			iconstr_new/4]).	
:-use_module('../../utils/template_inference',[max_min_linear_expression_list_all/6]).									
:- use_module(stdlib(numeric_abstract_domains),[
			nad_maximize/3,
			nad_entails/3]).		
:- use_module(stdlib(linear_expression),[negate_le/2]).							
:- use_module(stdlib(fraction),[greater_fr/2]).
:- use_module(library(apply_macros)).
:- use_module(library(lists)).	
	
%use  increments and resets procedure	
max_min_strategy(bound(Op,Lin_exp,Bounded),Head,Phase,[Fconstr],[Iconstr],Pending,Pending_out):-
	%we have to consider the case where the value is not reseted
	new_itvar(Aux_itvar),
	fconstr_new([Aux_itvar],Op,Lin_exp,Fconstr),
	% check the effect of the loops
	(Op=ub->
	check_loops_max(Phase,Head,Lin_exp,Resets,Pstrexp_pair2,Pending,Pending_out),
	(Resets=[] ->
	   Max_resets=Aux_itvar
	   ;
	   Max_resets=max([Aux_itvar|Resets])
	   ),
	Pstrexp_pair1=add([mult([Max_resets])])-add([])
	;
	check_loops_min(Phase,Head,Lin_exp,Resets,Pstrexp_pair2,Pending,Pending_out),
	(Resets=[] ->
	   Min_resets=Aux_itvar
	   ;
	   Min_resets=min([Aux_itvar|Resets])
	   ),
	Pstrexp_pair1=add([mult([Min_resets])])-add([])
	),
	pstrexp_pair_add(Pstrexp_pair1,Pstrexp_pair2,Pstrexp_pair),
	astrexp_new(Pstrexp_pair,Astrexp),
	iconstr_new(Astrexp,Op,Bounded,Iconstr).
    
    
    
check_loops_max([],_Head,_Lin_exp,[],Empty_pstrexp_pair,Pending,Pending):-
	pstrexp_pair_empty(Empty_pstrexp_pair).
	
check_loops_max([Loop|Loops],Head,Lin_exp,Resets,Pstrexp_pair,Pending,Pending_out):-
	check_loop_max(Loop,Head,Lin_exp,Resets1,Pstrexp_pair1,Pending,Pending_aux),
	check_loops_max(Loops,Head,Lin_exp,Resets2,Pstrexp_pair2,Pending_aux,Pending_out),
	append(Resets1,Resets2,Resets),
	pstrexp_pair_add(Pstrexp_pair1,Pstrexp_pair2,Pstrexp_pair).

%! check_loops_max(Loop:loop_id,Head:term,Call:term,Lin_exp:alinexp,Resets:list(itvar),Pstrexp_pair:pstrexp_pair,Pending:pending_constrs,Pending_out:pending_constrs)
% check the different possible behaviors of Loop with respect to Lin_exp
% * the loop does not increase Lin_exp: do nothing
% * the loop increases Lin_exp by a constant Delta: add maxsum(Loop,Delta) to the cost (in Pstrexp)
% * the loop increases Lin_exp by a linear expression Max_increment: add maxsum(Loop,Max_increment) to the cost
% * the loop resets Lin_exp to Max_resets: add Max_resets to the resets
check_loop_max(Loop,Head,Lin_exp,Resets,Pstrexp_pair,Pending,Pending_out):-
	%for linear recursion
	enriched_loop(Loop,Head,[Call],Cs),
	get_difference_version(Head,Call,Lin_exp,Lin_exp_diff),
	le_print_int(Lin_exp_diff,Exp_diff_int,_),
	negate_le(Lin_exp_diff,Lin_exp_diff_neg),
	le_print_int(Lin_exp_diff_neg,Exp_diff_neg_int,Exp_diff_denominator),
	term_variables((Head,Call),Vars),
% the lin_exp does not increase
	(nad_entails(Vars,Cs,[Exp_diff_int>=0])->
		(get_param(debug,[])->format('Loop ~p does not increase the expression~n',[Loop]);true),
		Resets=[],
		pstrexp_pair_empty(Pstrexp_pair),
		Pending_out=Pending
		;
% add a constant
		((nad_maximize([Exp_diff_neg_int=Exp_diff_denominator*D|Cs],[D],[Delta]),greater_fr(Delta,0))->
			(get_param(debug,[])->format('Loop ~p  increases the expression by ~p ~n',[Loop,Delta]);true),
			get_loop_itvar(Loop,Loop_name),
			Pstrexp_pair=add([mult([Loop_name,Delta])])-add([]),
			Resets=[],
			Pending_out=Pending
		;
			get_input_output_vars(Head,Input_vars_head,_),
			select_important_variables(Vars,Lin_exp,Vars_of_Interest),
			max_min_linear_expression_all(Lin_exp_diff_neg, Vars_of_Interest, Cs,max, Max_increments),
%add an expression		
			(Max_increments\=[]->
				(get_param(debug,[])->
				    ground_copy((Head,Call,Max_increments),(_,_,Max_increments_ground)),
				    format('Loop ~p  increases the expression by ~p ~n',[Loop,Max_increments_ground]);true),
				new_itvar(Aux_itvar),
				maplist(fconstr_new([Aux_itvar],ub),Max_increments,Maxsums),
				save_pending_list(sum,loop_vars(Head,[Call]),Loop,Maxsums,Pending,Pending_out),
				Pstrexp_pair=add([mult([Aux_itvar])])-add([]),
				Resets=[]
			;
%reset		
				copy_term((Head,Lin_exp),(Call,Lin_exp_p)),
				max_min_linear_expression_all(Lin_exp_p, Input_vars_head, Cs,max, Maxs_resets),
				Maxs_resets\=[],!,
				(get_param(debug,[])->
				    ground_copy((Head,Maxs_resets),(_,Maxs_resets_ground)),
				    format('Loop ~p  resets the expression to ~p ~n',[Loop,Maxs_resets_ground]);true),
				new_itvar(Aux_itvar),
				maplist(fconstr_new([Aux_itvar],ub),Maxs_resets,Maxtops),
				save_pending_list(max_min,Head,Loop,Maxtops,Pending,Pending_out),
				pstrexp_pair_empty(Pstrexp_pair),
				Resets=[Aux_itvar]
			)
		)
	).
				
%FIXME this can be improved				
check_loop_max(Loop,Head,Lin_exp,Resets,Pstrexp_pair,Pending,Pending_out):-
	%for multiple recursion
	enriched_loop(Loop,Head,Calls,Cs),
	Calls=[_,_|_],
	maplist(get_difference_version_aux(Head,Lin_exp),Calls,Lin_exp_diffs),
	term_variables((Head,Calls),Vars),
	exclude(is_positive(Vars,Cs),Lin_exp_diffs,Lin_exp_diffs_non_pos),
% the lin_exp does not increase
	(Lin_exp_diffs_non_pos=[]->
		(get_param(debug,[])->format('Loop ~p does not increase the expression~n',[Loop]);true),
		Resets=[],
		pstrexp_pair_empty(Pstrexp_pair),
		Pending_out=Pending
		;
% add a constant
		maplist(negate_le,Lin_exp_diffs_non_pos,Lin_exp_diffs_neg),
		(foldl(get_maximum_increase(Cs),Lin_exp_diffs_neg,0,Delta)->
			(get_param(debug,[])->format('Loop ~p  increases the expression by ~p ~n',[Loop,Delta]);true),
			get_loop_itvar(Loop,Loop_name),
			Pstrexp_pair=add([mult([Loop_name,Delta])])-add([]),
			Resets=[],
			Pending_out=Pending
		;
			get_input_output_vars(Head,Input_vars_head,_),
			select_important_variables(Input_vars_head,Lin_exp,Vars_of_Interest),
			max_min_linear_expression_list_all(Lin_exp_diffs_neg,Vars, Vars_of_Interest, Cs,max, Max_increments),
%add an expression		
			(Max_increments\=[]->
				(get_param(debug,[])->
				    ground_copy((Head,Max_increments),(_,Max_increments_ground)),
				    format('Loop ~p  increases the expression by ~p ~n',[Loop,Max_increments_ground]);true),
				new_itvar(Aux_itvar),
				maplist(fconstr_new([Aux_itvar],ub),Max_increments,Maxsums),
				save_pending_list(maxsum,Loop,((Head,Calls),Maxsums),Pending,Pending_out),
				Pstrexp_pair=add([mult([Aux_itvar])])-add([]),
				Resets=[]
			;
%reset		
				maplist(get_tail_version(Head,Lin_exp),Calls,Lin_exp_tails),
				max_min_linear_expression_list_all(Lin_exp_tails,Vars, Input_vars_head, Cs,max, Maxs_resets),
				Maxs_resets\=[],!,
				(get_param(debug,[])->
				    ground_copy((Head,Maxs_resets),(_,Maxs_resets_ground)),
				    format('Loop ~p  resets the expression to ~p ~n',[Loop,Maxs_resets_ground]);true),
				new_itvar(Aux_itvar),
				maplist(fconstr_new([Aux_itvar],ub),Maxs_resets,Maxtops),			
				save_pending_list(max,Loop,(Head,Maxtops),Pending,Pending_out),
				pstrexp_pair_empty(Pstrexp_pair),
				Resets=[Aux_itvar]
			)
		)
	).
				
		

is_positive(Vars,Cs,Lin_exp):-
	le_print_int(Lin_exp,Lin_exp_int,_),
	nad_entails(Vars,Cs,[Lin_exp_int>=0]).
	
get_maximum_increase(Cs,Lin_exp_neg,Delta,Delta2):-
	le_print_int(Lin_exp_neg,Exp_diff_neg_int,Exp_diff_denominator),
	nad_maximize([Exp_diff_neg_int=Exp_diff_denominator*D|Cs],[D],[Delta1]),
	greater_fr(Delta1,0),
	max_fr(Delta,Delta1,Delta2).				
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

check_loops_min([],_Head,_Lin_exp,[],Empty_pstrexp_pair,Pending,Pending):-
	pstrexp_pair_empty(Empty_pstrexp_pair).
	
check_loops_min([Loop|Loops],Head,Lin_exp,Resets,Pstrexp_pair,Pending,Pending_out):-
	check_loop_min(Loop,Head,Lin_exp,Resets1,Pstrexp_pair1,Pending,Pending_aux),
	check_loops_min(Loops,Head,Lin_exp,Resets2,Pstrexp_pair2,Pending_aux,Pending_out),
	append(Resets1,Resets2,Resets),
	pstrexp_pair_add(Pstrexp_pair1,Pstrexp_pair2,Pstrexp_pair).

%! check_loop_min(Loop:loop_id,Head:term,Lin_exp:alinexp,Resets:list(itvar),Pstrexp_pair:pstrexp_pair,Pending:pending_constrs,Pending_out:pending_constrs)
% check the different possible behaviors of Loop with respect to Lin_exp
% similar to check_loops_max
check_loop_min(Loop,Head,Lin_exp,Resets,Pstrexp_pair,Pending,Pending_out):-
	enriched_loop(Loop,Head,[Call],Cs),
	get_difference_version(Head,Call,Lin_exp,Lin_exp_diff),
	le_print_int(Lin_exp_diff,Exp_diff_int,Exp_diff_denominator),
	%negate_le(Lin_exp_diff,Lin_exp_diff_neg),
	%le_print_int(Lin_exp_diff_neg,Exp_diff_neg_int,Exp_diff_denominator),
	term_variables((Head,Call),Vars),
% the Lin_exp does not decrease
	(nad_entails(Vars,Cs,[Exp_diff_int=<0])->
		(get_param(debug,[])->format('Loop ~p does not decrease the expression~n',[Loop]);true),
		Resets=[],
		pstrexp_pair_empty(Pstrexp_pair),
		Pending_out=Pending
		;
% decreases by a constant
		((nad_maximize([Exp_diff_int=Exp_diff_denominator*D|Cs],[D],[Delta]),greater_fr(Delta,0))->
			(get_param(debug,[])->format('Loop ~p  decreases the expression by ~p ~n',[Loop,Delta]);true),
			get_loop_itvar(Loop,Loop_name),
			Pstrexp_pair=add([])-add([mult([Loop_name,Delta])]),
			Resets=[],
			Pending_out=Pending
		;
			get_input_output_vars(Head,Input_vars_head,_),
			select_important_variables(Input_vars_head,Lin_exp,Vars_of_Interest),
			max_min_linear_expression_all(Lin_exp_diff, Vars_of_Interest, Cs,max, Max_increments),
%decreases by an expression		
			(Max_increments\=[]->
				(get_param(debug,[])->
					ground_copy((Head,Call,Max_increments),(_,_,Max_increments_ground)),
					format('Loop ~p  decreases the expression by ~p ~n',[Loop,Max_increments_ground]);true),
				new_itvar(Aux_itvar),
				maplist(fconstr_new([Aux_itvar],ub),Max_increments,Maxsums),
				save_pending_list(sum,loop_vars(Head,[Call]),Loop,Maxsums,Pending,Pending_out),
				Pstrexp_pair=add([])-add([mult([Aux_itvar])]),
				Resets=[]
			;
%reset		
				copy_term((Head,Lin_exp),(Call,Lin_exp_p)),
				max_min_linear_expression_all(Lin_exp_p, Input_vars_head, Cs,min, Mins_resets),
				Mins_resets\=[],!,
				(get_param(debug,[])->
					ground_copy((Head,Mins_resets),(_,Mins_resets_ground)),
					format('Loop ~p  resets the expression to ~p ~n',[Loop,Mins_resets_ground]);true),
				new_itvar(Aux_itvar),
				maplist(fconstr_new([Aux_itvar],lb),Mins_resets,Maxtops),
				save_pending_list(max_min,Head,Loop,Maxtops,Pending,Pending_out),
				pstrexp_pair_empty(Pstrexp_pair),
				Resets=[Aux_itvar]
			)
		)
	).    