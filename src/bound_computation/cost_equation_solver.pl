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


:- module(cost_equation_solver,[get_loop_cost/5,init_cost_equation_solver/0]).

:- use_module(constraints_maximization,[
			max_min_fconstrs_in_cost_equation/6,
			max_min_linear_expression_all/5]).
:- use_module('../IO/params',[get_param/2]).
:- use_module('../IO/output',[print_warning_in_error_stream/2]).
:- use_module('../db',[eq_ph/8,
			     loop_ph/6,
			     upper_bound/4,
			     external_upper_bound/3,
			     get_input_output_vars/3]).

:- use_module('../utils/cofloco_utils',[tuple/3,ground_copy/2]).
:- use_module('../utils/cost_structures',[cstr_extend_variables_names/3,
			cstr_empty/1,
			cstr_simplify/2,
			cstr_or_compress/2,
			max_min_ub_lb/2,
			bconstr_accum_bounded_set/3]).


:- use_module(stdlib(fraction),[sum_fr/3]).
:- use_module(stdlib(linear_expression),[write_le/2]).
:- use_module(stdlib(utils),[ut_flat_list/2]).
:- use_module(stdlib(set_list)).
:- use_module(stdlib(numeric_abstract_domains),[nad_glb/3,nad_consistent_constraints/1]).

:-use_module(library(apply_macros)).
:-use_module(library(lists)).

%! equation_cost(Head:term,Call:term,Forward_inv_hash:(int,polyhedron),Eq_id:equation_id,Cost:cstr)
% store the cost structure of a cost equation application given a local invariant
% for cacheing purposes
:- dynamic loop_cost/5.

%! init_cost_equation_solver
% clear all the stored intermediate results
init_cost_equation_solver:-
	retractall(loop_cost(_,_,_,_,_)).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! get_loop_cost(+Head:term,+Calls:list(term),+Forward_inv_hash:(int,polyhedron),+Loop_id:loop_id,-Cost:cstr) is det
%  Given a loop id (Eq_id) , it accesses the definition and computes the cost of an individual loop application
% a loop corresponds to one or more cost equations that behave the same way with respect to the recursive call
get_loop_cost(Head,Calls,(Forward_inv_hash,Forward_inv),Loop_id,Cost):-
	loop_cost(Head,Calls,(Forward_inv_hash,Forward_inv2),Loop_id,Cost),
	Forward_inv==Forward_inv2,!.

get_loop_cost(Head,Calls,(Forward_inv_hash,Forward_inv),Loop_id,Final_cost):-
    loop_ph(Head,(Loop_id,_),Calls,_Inv,Eqs,_),
    maplist(get_equation_cost(Head,Calls,Forward_inv),Eqs,Costs),
    cstr_or_compress(Costs,Final_cost),
    assert(loop_cost(Head,Calls,(Forward_inv_hash,Forward_inv),Loop_id,Final_cost)).
    
%! get_equation_cost(+Head:term,+Calls:list(term),+Forward_inv:polyhedron,+Eq_id:eq_id,-Cost:cstr) is det
%  * each call in the equation is substituted by its cost structure
%  * the final constraints of the cost expressions are combined and the costs added 
 get_equation_cost(Head,Calls,Forward_inv,Eq_id,Cost):-
    eq_ph(Head,(Eq_id,_),Basic_cost, Base_calls,Calls,_,Phi,_),
	nad_glb(Forward_inv,Phi,Phi1),
	(nad_consistent_constraints(Phi1)->
		term_variables((Head,Calls),TVars),
		foldl(accumulate_calls(Eq_id),Base_calls,(Basic_cost,1),(cost(Ub_fconstrs_list,Lb_fconstrs_list,Iconstrs,Bases,Base),_)),
		% we reverse the calls in case we want to combine cost structures incrementally
		% this is not done now but it would allow us to detect which calls make us lose precision
		%reverse(Base_calls,Base_calls_inv),
		max_min_fconstrs_in_cost_equation(Ub_fconstrs_list,Base_calls,Phi1,TVars,New_Ub_fconstrs,New_iconstrs1),
		%for finding interesting examples
		get_lost_fconstrs_expressable_as_outputs(Eq_id,Ub_fconstrs_list,New_Ub_fconstrs,Base_calls,Phi),
		max_min_fconstrs_in_cost_equation(Lb_fconstrs_list,Base_calls,Phi1,TVars,New_Lb_fconstrs,New_iconstrs2),
		ut_flat_list([New_iconstrs1,New_iconstrs2,Iconstrs],New_iconstrs),
		cstr_simplify(cost(New_Ub_fconstrs,New_Lb_fconstrs,New_iconstrs,Bases,Base),Cost)
	;
		cstr_empty(Cost)
	).
	
accumulate_calls(Eq_id,(Call,chain(Chain)),(cost(Ub_fconsts1,Lb_fconsts1,Iconstrs1,Bases1,Base1),N),(cost([Ub_fconsts2|Ub_fconsts1],[Lb_fconsts2|Lb_fconsts1],[Iconstrs2|Iconstrs1],Bases,Base),N1)) :-
    N1 is N+1,
    upper_bound(Call,Chain,_Hash,Cost_call),
    % we extend the names of the intermediate variables to ensure they are unique
    cstr_extend_variables_names(Cost_call,eq(Eq_id,N),cost(Ub_fconsts2,Lb_fconsts2,Iconstrs2,Bases2,Base2)),
    sum_fr(Base1,Base2,Base),
    append(Bases2,Bases1,Bases).

accumulate_calls(Eq_id,(Call,external_pattern(Id)),(cost(Ub_fconsts1,Lb_fconsts1,Iconstrs1,Bases1,Base1),N),(cost([Ub_fconsts2|Ub_fconsts1],[Lb_fconsts2|Lb_fconsts1],[Iconstrs2|Iconstrs1],Bases,Base),N1)) :-
    N1 is N+1,
    external_upper_bound(Call,Id,Cost_call),
    % we extend the names of the intermediate variables to ensure they are unique
    cstr_extend_variables_names(Cost_call,eq(Eq_id,N),cost(Ub_fconsts2,Lb_fconsts2,Iconstrs2,Bases2,Base2)),
    sum_fr(Base1,Base2,Base),
    append(Bases2,Bases1,Bases).   
    


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



