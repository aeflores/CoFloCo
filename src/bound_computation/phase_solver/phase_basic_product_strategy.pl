/** <module> phase_basic_product_strategy

This module implements 3 strategies: basic_product_strategy, level_product_strategy
and leaf product strategy
-basic_product_strategy reduces the sum of a linear expression Lin_exp to the
product of the number of iterations of the loop and the maximum/minimum value of Lin_exp

-level_sum_strategy reduces the sum of a linear expression Lin_exp over a complete phase execution
into the sum of the linear expression in one level of the execution tree multiplied by the depth of the execution.

-leaf_product_strategy reduces the sum of a linear expression over one level to
the number of elements of this level multiplied by the maximum/minimum value of the expression
This is only valid for the last level, the leafs of the evaluation tree

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

:- module(phase_basic_product_strategy,[
	basic_product_strategy/8
	]).

:- use_module(phase_common).
:- use_module(phase_solver,[
	state_save_pending_list/7,
	state_save_new_iconstrs/3
	]).
		        
:- use_module('../constraints_maximization',[max_min_linear_expression_all/5]).		
:- use_module('../../utils/cost_structures',[
	new_itvar/1,
	get_loop_itvar/2,
	astrexp_new/2,
	fconstr_new/4,
	iconstr_new/4
	]).	
:- use_module('../../refinement/loops',[
	loop_ioVars/2
	]).					
:- use_module('../../IO/params',[get_param/2]).		
:- use_module('../../IO/output',[
	print_product_strategy_message/3,
	print_or_log/2,
	interesting_example_warning/2
	]).		
:- use_module(stdlib(list_map),[lookup_lm/3]).
:- use_module(library(apply_macros)).
:- use_module(library(lists)).	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%! basic_product(Head,Call,Loop,Lin_exp,Bounded,Aux_exp,Max_min,Pending,Pending_out)
% Implement the basic product strategy:
% maxsum(A)=< maxsum(1)*max(A)
% minsum(A)=< minsum(1)*min(A)

basic_product_strategy(bound(Op,Lin_exp,Bounded),Depth,loop_vars(Head,Calls),Loop_id,Phase_loops,State,State3,Changes):-	
    (get_param(debug,[])->print_or_log('   - Applying basic product strategy ~n',[]);true),
	get_constr_op(Max_min,Op),
	lookup_lm(Phase_loops,Loop_id,Loop),
	Loop=loop(Head,Calls,Cs,_),
	new_itvar(Aux_itvar),
	get_loop_itvar(Loop_id,Loop_itvar),
	astrexp_new(add([mult([Loop_itvar,Aux_itvar])])-add([]),Astrexp),
	loop_ioVars(Loop,IOvars),
	(is_input_head_expression(Head,IOvars,Lin_exp)->
		fconstr_new([Aux_itvar],Op,Lin_exp,Fconstr),
		Max_fconstrs=[Fconstr]
	;
	 copy_term(IOvars,ioVars(Head,Vars_head,_)),
	 max_min_linear_expression_all(Lin_exp, Vars_head, Cs,Max_min, Maxs_exps),
	 %WARNING to find interesting examples
	 interesting_example_warning(failed_maximization,(Maxs_exps,Lin_exp,Loop,Head,Calls)),
	 maplist(fconstr_new([Aux_itvar],Op),Maxs_exps,Max_fconstrs)
	 ),
	Depth2 is Depth+1,
	state_save_pending_list(State,max_min,Depth2,loop_vars(Head,Calls),Loop_id,Max_fconstrs,State2),
    Aux_exp=bound(Op,Astrexp,Bounded),
    state_save_new_iconstrs(State2,[Aux_exp],State3),
    print_product_strategy_message(Head,max_min,Max_fconstrs),
    Changes=[new_iconstrs([Aux_exp])].
