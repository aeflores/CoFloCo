/** <module> phase_basic_product_strategy

This module implements 2 strategies: basic_product_strategy and level_product_strategy
-basic_product_strategy reduces the sum of a linear expression Lin_exp to the
product of the number of iterations of the loop and the maximum/minimum value of Lin_exp

-level_sum_strategy reduces the sum of a linear expression Lin_exp over a complete phase execution
into the sum of the linear expression in one level of the execution tree multiplied by the depth of the execution.

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
		basic_product_strategy/6,
		level_product_strategy/6
	]).

:- use_module(phase_common).
:- use_module(phase_solver,[				
				enriched_loop/4,
		        save_pending_list/6]).
		        
:- use_module('../constraints_maximization',[max_min_linear_expression_all/5]).		
:- use_module('../../utils/cost_structures',[
			new_itvar/1,
			get_loop_itvar/2,
			get_loop_depth_itvar/2,
			astrexp_new/2,
			fconstr_new/4,
			iconstr_new/4]).	
:- use_module('../../IO/params',[get_param/2]).							
:- use_module(library(apply_macros)).
:- use_module(library(lists)).	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%! basic_product(Head,Call,Loop,Lin_exp,Bounded,Aux_exp,Max_min,Pending,Pending_out)
% Implement the basic product strategy:
% maxsum(A)=< maxsum(1)*max(A)
% minsum(A)=< minsum(1)*min(A)


basic_product_strategy(bound(Op,Lin_exp,Bounded),loop_vars(Head,Calls),Loop,Aux_exp,Pending,Pending_out):-	
	get_constr_op(Max_min,Op),
	enriched_loop(Loop,Head,Calls,Cs),
	new_itvar(Aux_itvar),
	get_loop_itvar(Loop,Loop_itvar),
	astrexp_new(add([mult([Loop_itvar,Aux_itvar])])-add([]),Astrexp),
	(is_head_expression(Head,Lin_exp)->
		fconstr_new([Aux_itvar],Op,Lin_exp,Fconstr),
		Max_fconstrs=[Fconstr]
	;
	 Head=..[_|Vars_head],
	 max_min_linear_expression_all(Lin_exp, Vars_head, Cs,Max_min, Maxs_exps),
	 maplist(fconstr_new([Aux_itvar],Op),Maxs_exps,Max_fconstrs)
	 ),
	save_pending_list(max_min,Head,Loop,Max_fconstrs,Pending,Pending_out),
    Aux_exp=bound(Op,Astrexp,Bounded),
    (get_param(debug,[])->	
			format('~p is bounded by ~p*~p  ~n',[Bounded,Loop_itvar,Aux_itvar])
	;
	true).
    
 level_product_strategy(bound(Op,Lin_exp,Bounded),loop_vars(Head,Calls),Loop,Iconstr,Pending,Pending_out):-
	%FIXME needs flag for the multiple recursion
	Calls=[_,_|_],
	get_constr_op(Max_min,Op),
	enriched_loop(Loop,Head,Calls,Cs),
	new_itvar(Aux_itvar),

	get_loop_depth_itvar(Loop,Loop_itvar),
	astrexp_new(add([mult([Loop_itvar,Aux_itvar])])-add([]),Astrexp),
	(is_head_expression(Head,Lin_exp)->
		fconstr_new([Aux_itvar],Op,Lin_exp,Fconstr),
		Max_fconstrs=[Fconstr]
	;
	 Head=..[_|Vars_head],
	 max_min_linear_expression_all(Lin_exp, Vars_head, Cs,Max_min, Maxs_exps),
	 maplist(fconstr_new([Aux_itvar],Op),Maxs_exps,Max_fconstrs)
	 ),
	save_pending_list(level,Head,0,Max_fconstrs,Pending,Pending_out),
    Iconstr=bound(Op,Astrexp,Bounded),
    (get_param(debug,[])->	
			format('~p is bounded by ~p*~p  ~n',[Bounded,Loop_itvar,Aux_itvar]);
	true).
    