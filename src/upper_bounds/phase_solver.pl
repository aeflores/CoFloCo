/** <module> phase_solver

This module computes the cost structure of a phase in terms of the variables 
at the beginning and the end of the phase.


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

:- module(phase_solver,[compute_phases_cost/5,init_phase_solver/0]).

					
:- use_module(cost_equation_solver,[get_equation_cost/5]).
:- use_module(constraints_maximization,[max_min_linear_expression_all/5]).		
				      
:- use_module('../db',[
			   phase_loop/5,
		       loop_ph/6]).

:- use_module('../IO/params',[get_param/2]).		
:- use_module('../ranking_functions',[
				      ranking_function/4,
				      partial_ranking_function/7]).	
				      		
:-use_module('../refinement/invariants',[
			      phase_transitive_closure/5,
%			      get_phase_star/4,
			      forward_invariant/4]).			
	
:- use_module('../utils/cofloco_utils',[
			tuple/3,
			bagof_no_fail/3]).	
:- use_module('../utils/cost_structures',[
			cstr_extend_variables_names/3,
			cstr_extract_top_maxs/3,
		    cstr_extract_top_mins/3,
			cstr_remove_cycles/2,
			cstr_name_aux_var/1,
			cstr_get_it_name/2,
			cstr_propagate_summatory/4,
			cstr_generate_top_exp/4,
			cstr_empty/1,
			cstr_join/3]).			
:-use_module('../utils/template_inference',[
	difference_constraint2_farkas_dmatrix/5
	]).						


:- use_module(stdlib(numeric_abstract_domains),[
						nad_maximize/3,
						nad_entails/3,
						nad_consistent_constraints/1]).
:- use_module(stdlib(linear_expression),[
	integrate_le/3,
	write_le/2,
	multiply_le/3,
	subtract_le/3,
	negate_le/2]).							
:- use_module(stdlib(fraction),[inverse_fr/2,greater_fr/2]).
:- use_module(stdlib(set_list)).
:- use_module(stdlib(profiling),[profiling_start_timer/1,profiling_stop_timer_acum/2]).
:- use_module(stdlib(counters),[counter_increase/3]).
:- use_module(stdlib(utils),[ut_flat_list/2,ut_split_at_pos/4]).

%! phase_cost(Phase:phase,Head:term,Call:term,Forward_inv_hash:(int,polyhedron),Cost:cost_structure)
% store the cost structure of a phase given a local invariant
% for cacheing purposes
:- dynamic  phase_cost/5.



%! init_phase_solver is det
% clear all the intermediate results
init_phase_solver:-
	retractall(phase_cost(_,_,_,_,_,_)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! compute_phases_cost(+Phases:list(phase),+Chain:chain,+Head:term,+Call:term,-Costs:list(cost_structure)) is det
% compute cost structures for the phases Phases that belong to Chain.
% the internal parts of the cost structure are directly expressed in terms of the input variables of the chain
% the constraints of the cost structure are expressed in terms of the variables at the beginnig and end of the chain (Head and Call)
compute_phases_cost([],_,_,_,[]).
compute_phases_cost([Phase|More],Chain,Head,Call,[Cost|Costs]):-
	forward_invariant(Head,([Phase|More],_),Forward_inv_hash,Forward_inv),
	%obtain a cost structure in terms of the variables at the beginning and end of the phase
	compute_phase_cost(Phase,Head,Call,(Forward_inv_hash,Forward_inv),Cost),	
	compute_phases_cost(More,Chain,Head,Call,Costs).
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%! compute_phase_cost(Phase:phase,Head:term,Call:term,Forward_inv_hash:(int,polyhedron),Cost:cost_structure) is det
% Obtain the cost of a phase given a forward invariant.
% if the phase is non-iterative, the cost is the cost of the equation, otherwise:
% * get the cost of all the equations
% * put each cost into a new loop
% * try to take loops out by inductive compression
% * try to compress constraints from different loops
compute_phase_cost(Phase,Head,Call,(Forward_hash,Forward_inv),Cost):-
	phase_cost(Phase,Head,Call,(Forward_hash,Forward_inv2),Cost),
	Forward_inv2==Forward_inv,!,
	counter_increase(compressed_phases1,1,_).
% in a non-iterative phase, we just obtain the cost of the equation
compute_phase_cost(Non_it,Head,Call,(Forward_hash,Forward_inv),Cost):-
	number(Non_it),	
	profiling_start_timer(equation_cost),
	get_equation_cost(Head,Call1,(Forward_hash,Forward_inv),Non_it,Cost),
	(Call1\=none->Call1=Call;true),
	profiling_stop_timer_acum(equation_cost,_),
	assert(phase_cost(Non_it,Head,Call,(Forward_hash,Forward_inv),Cost)).

compute_phase_cost(Phase,Head,Call,(Forward_hash,Forward_inv),Cost):-
    %get the cost of each iterative component of the phase	
	profiling_start_timer(equation_cost),
	maplist(get_equation_loop_cost(Head,Call,(Forward_hash,Forward_inv)),Phase,Costs),
	profiling_stop_timer_acum(equation_cost,_),
	max_min_costs_in_phase(Costs,Head,Call,Forward_inv,Phase,Cost),
	assert(phase_cost(Phase,Head,Call,(Forward_hash,Forward_inv),Cost)).

get_equation_loop_cost(Head,Call,(Forward_hash,Forward_inv),Eq_id,Cost2):-
	get_equation_cost(Head,Call,(Forward_hash,Forward_inv),Eq_id,Cost),
	cstr_extend_variables_names(Cost,it(Eq_id),Cost2).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

max_min_costs_in_phase(Costs,Head,Call,_Forward_inv,Phase,Cost_final):-
	maplist(cstr_remove_cycles,Costs,Costs_simple),
	maplist(cstr_propagate_summatory,Phase,Costs_simple,Costs_propagated,Summatories_pairs),
	maplist(cstr_extract_top_maxs,Costs_propagated,Costs_propagated1,Maxs),
	maplist(cstr_extract_top_mins,Costs_propagated1,Costs_propagated2,Mins),
	maplist(tuple,Summatories_max,Summatories_min,Summatories_pairs),
	maplist(get_it_sum_constraint(ub),Phase,It_cons_max),
	maplist(append,It_cons_max,Summatories_max,Summatories_max1),
	maplist(get_it_sum_constraint(lb),Phase,It_cons_min),
	maplist(append,It_cons_min,Summatories_min,Summatories_min1),
	cstr_empty(Empty_cost),
	foldl(cstr_join,Costs_propagated2,Empty_cost,cost([],[],Aux_exps,Bases,Base)),
	compute_sums_and_max_min_in_phase(Head,Call,Phase,Maxs,Mins,Summatories_max1,Summatories_min1,Final_top_max,Final_top_min,New_auxs),
	append(New_auxs,Aux_exps,Aux_exps_final),
	cstr_remove_cycles(cost(Final_top_max,Final_top_min,Aux_exps_final,Bases,Base),Cost_final).
	
get_it_sum_constraint(ub,Loop,[bound(ub,[]+1,[Loop_name])]):-
	cstr_get_it_name(Loop,Loop_name).
get_it_sum_constraint(lb,Loop,[bound(lb,[]+1,[Loop_name])]):-
	cstr_get_it_name(Loop,Loop_name).	
	
	
compute_sums_and_max_min_in_phase(Head,Call,Phase,Maxs,Mins,Summatories_max,Summatories_min,Final_top_max,Final_top_min,New_auxs):-
	maplist(save_pending_list(max,Head,Call),Maxs),
	maplist(save_pending_list(min,Head,Call),Mins),
	maplist(save_pending_list(maxsum,Head,Call),Phase,Summatories_max),
	maplist(save_pending_list(minsum,Head,Call),Phase,Summatories_min),
	%special treatment of ranking functions
	rf_limit(Max),
	get_ranking_functions_constraints(Max,Head,Call,Phase,_,Top),
	maplist(save_new_phase_top(Head,Call,Phase),Top),
	get_ranking_functions_lower_constraints(Max,Head,Call,Phase,_,LTop),
	maplist(save_new_phase_top(Head,Call,Phase),LTop),
	compute_all_pending(Head,Call,Phase),
	collect_phase_results(Head,Call,Phase,Final_top_max,Final_top_min,New_auxs).

		
compute_all_pending(Head,Call,Phase):-
	compute_pending(Head,Call,Phase),
	compute_all_pending(Head,Call,Phase).

compute_all_pending(_,_,_).

compute_pending(Head,Call,Phase):-
	retract(pending(Type,Head,Call,bound(_Op,Exp,Bounded))),

	copy_term((Head,Call,Exp),(Head2,Call2,Exp2)),
	write_le(Exp2,Exp2_print),
	numbervars((Head2,Call2),0,_),
	writeln(computing(Type,Exp2_print)),
	compute_pending_element(Type,Head,Call,Phase,Exp,Bounded,New_tops,New_auxs),
	maplist(save_new_phase_top(Head,Call,Phase),New_tops),
	maplist(save_new_phase_aux(Head,Call,Phase),New_auxs).

compute_pending_element(maxsum(Loop),Head,Call,Phase,Exp,Bounded,New_tops,New_auxs):-
	compute_maxsum(Head,Call,Phase,Loop,Exp,Bounded,New_tops,New_auxs).
compute_pending_element(minsum(Loop),Head,Call,Phase,Exp,Bounded,New_tops,New_auxs):-
	compute_minsum(Head,Call,Phase,Loop,Exp,Bounded,New_tops,New_auxs).	
compute_pending_element(max,Head,Call,Phase,Exp,Bounded,New_tops,New_auxs):-
	compute_max(Head,Call,Phase,Exp,Bounded,New_tops,New_auxs).	
compute_pending_element(min,Head,Call,Phase,Exp,Bounded,New_tops,New_auxs):-
	compute_min(Head,Call,Phase,Exp,Bounded,New_tops,New_auxs).	
		
%partial ranking function (a special case of linear sum)
compute_maxsum(Head,Call,Phase,Loop,[]+1,Bounded,New_tops,New_auxs):-!,
	bagof_no_fail(Rf,
	Deps^Deps_type^Loops^
	(
			partial_ranking_function(Head,_Chain,Phase,Loops,Rf,Deps,Deps_type),
			contains_sl(Loops,Loop)		
			),Rfs),
	maplist(get_difference_version(Head,Call),Rfs,Rfs_diff),
	append(Rfs,Rfs_diff,Rfs_all),
	check_rest_loops(Rfs_all,Head,Call,Phase,Loop,Bounded,[],[],New_tops,New_auxs).

%linear sum
compute_maxsum(Head,Call,Phase,Loop,Lin_exp,Bounded,New_tops,New_auxs):-
	is_difference(Head,Call,Lin_exp,Loop,Exp_list),
	check_rest_loops(Exp_list,Head,Call,Phase,Loop,Bounded,[],[],New_tops,New_auxs),
	%we stay with this option as long as one attempt succeeded 
	%otherwise go to simple multiplication
	New_tops\=[].
	
%simple multiplication
compute_maxsum(Head,Call,_,Loop,Lin_exp,Bounded,[],[Aux_exp]):-
	cstr_name_aux_var(Aux_name),
	cstr_get_it_name(Loop,Loop_name),
	Internal_exp=exp([(Aux_name,Aux_var),(Loop_name,It_var)],[],add([mult([It_var,Aux_var])]),add([])),
    Aux_exp=bound(ub,Internal_exp,Bounded),
    save_pending(max,Head,Call,bound(ub,Lin_exp,[Aux_name])).

check_rest_loops([],_Head,_Call,_Phase,_Loop,_Bounded,Tops,Auxs,Tops,Auxs).
check_rest_loops([Exp|Exp_list],Head,Call,Phase,Loop,Bounded,Accum_tops,Accum_auxs,New_tops_out,New_auxs_out):-
		check_rest_loops_1(Phase,Loop,Head,Call,Exp,exp([],[],add([]),add([])),Bounded,Accum_tops,Accum_auxs,Tops1,Auxs1),!,
		check_rest_loops(Exp_list,Head,Call,Phase,Loop,Bounded,Tops1,Auxs1,New_tops_out,New_auxs_out).
%if it fails, we try with the rest		
check_rest_loops([_Exp|Exp_list],Head,Call,Phase,Loop,Bounded,Accum_tops,Accum_auxs,New_tops_out,New_auxs_out):-
		check_rest_loops(Exp_list,Head,Call,Phase,Loop,Bounded,Accum_tops,Accum_auxs,New_tops_out,New_auxs_out).
		
check_rest_loops_1([],_Loop,_Head,_Call,Exp,Carry_exp,Bounded,Accum_tops,Accum_auxs,Tops,Auxs):-	
		Carry_exp==exp([],[],add([]),add([])),
		Tops=[bound(ub,Exp,Bounded)|Accum_tops],
		Auxs=Accum_auxs.
check_rest_loops_1([],_Loop,_Head,_Call,Exp,Carry_exp,Bounded,Accum_tops,Accum_auxs,Tops,Auxs):-	
		cstr_name_aux_var(Aux_name),
		Carry_exp=exp(Pos_Index,Neg_index,add(Summands),Add_neg),
		New_exp=exp([(Aux_name,Aux_var)|Pos_Index],Neg_index,add([mult([Aux_var])|Summands]),Add_neg),
		Tops=[bound(ub,Exp,[Aux_name])|Accum_tops],
		Auxs=[bound(ub,New_exp,Bounded)|Accum_auxs].		
	
check_rest_loops_1([Loop|Loops],Loop,Head,Call,Exp,Carry_exp,Bounded,Accum_tops,Accum_auxs,Tops,Auxs):-!,
		check_rest_loops_1(Loops,Loop,Head,Call,Exp,Carry_exp,Bounded,Accum_tops,Accum_auxs,Tops,Auxs).
		
check_rest_loops_1([Loop2|Loops],Loop,Head,Call,Exp,Carry_exp,Bounded,Accum_tops,Accum_auxs,Tops,Auxs):-	
		(is_head_expression(Head,Exp)->
			get_difference_version(Head,Call,Exp,Exp_diff)
			;
			Exp_diff=Exp
		),
		loop_ph(Head,(Loop2,_),Call,Cs,_,_),
		Carry_exp=exp(Pos_Index,Neg_index,add(Summands),Add_neg),	
		negate_le(Exp_diff,Exp_diff_neg),
		term_variables((Head,Call),Vars),
		%collaborative loop
		le_print_int(Exp_diff,Exp_diff_print_int,_),
		(nad_entails(Vars,Cs,[Exp_diff_print_int>=0])->
			(find_maxsum_constraint(Loop2,Head,Call,Cs,Exp_diff,New_bounded)->			
				append(New_bounded,Bounded,Bounded1)
				;
				Bounded1=Bounded
			),
			check_rest_loops_1(Loops,Loop,Head,Call,Exp,Carry_exp,Bounded1,Accum_tops,Accum_auxs,Tops,Auxs)
		;
		%add a constant
		le_print_int(Exp_diff_neg,Exp_diff_neg_int,Exp_diff_denominator),
		(nad_maximize([Exp_diff_neg_int=Exp_diff_denominator*D|Cs],[D],[Delta])->
			cstr_get_it_name(Loop2,Loop_name),
			Carry_exp1=exp([(Loop_name,Loop_var)|Pos_Index],Neg_index,add([mult([Loop_var,Delta])|Summands]),Add_neg),
			check_rest_loops_1(Loops,Loop,Head,Call,Exp,Carry_exp1,Bounded,Accum_tops,Accum_auxs,Tops,Auxs)
		;
		%add an expression	
		term_variables(Head,Vars_head),from_list_sl(Vars_head,Vars_head_set),
		term_variables(Exp_diff_neg,Vars_exp),from_list_sl(Vars_exp,Vars_exp_set),
		difference_sl(Vars_head_set,Vars_exp_set,Vars_of_Interest),
		((max_min_linear_expression_all(Exp_diff_neg, Vars_of_Interest, Cs,max, Maxs),Maxs\=[])->
			cstr_name_aux_var(Aux_name),
			Carry_exp1=exp([(Aux_name,Aux_var)|Pos_Index],Neg_index,add([mult([Aux_var])|Summands]),Add_neg),
			maplist(cstr_generate_top_exp([Aux_name],ub),Maxs,Maxsums),
			save_pending_list(maxsum,Head,Call,Loop2,Maxsums),
			check_rest_loops_1(Loops,Loop,Head,Call,Exp,Carry_exp1,Bounded,Accum_tops,Accum_auxs,Tops,Auxs)
		;
		%reset
		%FIXME
		fail
		)
		)
		).	

			
is_head_expression(Head,Exp):-
	copy_term((Head,Exp),(Head2,Exp2)),
	numbervars(Head2,0,_),
	ground(Exp2).
	
			
find_maxsum_constraint(Loop,Head,Call,Cs,Exp_diff,Bounded):-
		pending(maxsum(Loop),Head,Call,bound(ub,Exp2,Bounded)),
		term_variables((Head,Call),Vars),
		le_print_int(Exp2,Exp2_print_int,_),
		nad_entails(Vars,Cs,[Exp2_print_int>=0]),
		subtract_le(Exp_diff,Exp2,Exp_diff2),
		le_print_int(Exp_diff2,Exp_diff2_print_int,_),
		nad_entails(Vars,Cs,[Exp_diff2_print_int>=0]),!.


%FIXME implement	
%compute_minsum(Head,Call,Phase,Loop,[]+1,Bounded,New_tops,New_auxs):-!,
%compute_minsum(Head,Call,Phase,Loop,Lin_exp,Bounded,New_tops,New_auxs):-

compute_minsum(Head,Call,_,Loop,Lin_exp,Bounded,[],[Aux_exp]):-
	cstr_name_aux_var(Aux_name),
	cstr_get_it_name(Loop,Loop_name),
	Internal_exp=exp([(Aux_name,Aux_var),(Loop_name,It_var)],[],add([mult([It_var,Aux_var])]),add([])),
    Aux_exp=bound(lb,Internal_exp,Bounded),
    save_pending(min,Head,Call,bound(lb,Lin_exp,[Aux_name])).


%FIXME implement the advanced one
compute_max(Head,Call,Phase,Lin_exp,Bounded,New_tops,[]):-
	max_min_top_expression_in_phase(Head,Call,Phase,bound(ub,Lin_exp,Bounded),New_tops),
	New_tops\=[].
	
compute_max(Head,Call,Phase,Lin_exp,Bounded,[],[Aux_exp]):-

	check_loops_max(Phase,Head,Call,Lin_exp,Resets,Additions),
	%we have to consider the case where the value is not reseted
	generate_index([Lin_exp|Resets],[],Reset_vars,Index1),
	generate_index(Additions,Index1,Addition_vars,Index2),
	maplist(put_inside_mult,Addition_vars,Summands),
	(Reset_vars=[_]->
	Internal_exp=exp(Index2,[],add([mult(Reset_vars)|Summands]),add([]))
	;
	Internal_exp=exp(Index2,[],add([mult([max(Reset_vars)])|Summands]),add([]))
	),
    Aux_exp=bound(ub,Internal_exp,Bounded).
    
%failed    
compute_max(_Head,_Call,_Phase,_Lin_exp,_Bounded,[],[]).
	
compute_min(Head,Call,Phase,Lin_exp,Bounded,New_tops,[]):-
	max_min_top_expression_in_phase(Head,Call,Phase,bound(lb,Lin_exp,Bounded),New_tops).
			
	
check_loops_max([],_Head,_Call,_Lin_exp,[],[]).
%nothing happens
check_loops_max([Loop|Loops],Head,Call,Lin_exp,Resets,Additions):-
	loop_ph(Head,(Loop,_),Call,Cs,_,_),
	get_difference_version(Head,Call,Lin_exp,Lin_exp_diff),
	le_print_int(Lin_exp_diff,Exp_diff_int,_),
	term_variables((Head,Call),Vars),
	nad_entails(Vars,Cs,[Exp_diff_int>=0]),!,
	check_loops_max(Loops,Head,Call,Lin_exp,Resets,Additions).

% add a constant
%FIXME take D into account
check_loops_max([Loop|Loops],Head,Call,Lin_exp,Resets,[Loop_name|Additions]):-
	loop_ph(Head,(Loop,_),Call,Cs,_,_),
	get_difference_version(Head,Call,Lin_exp,Lin_exp_diff),
	negate_le(Lin_exp_diff,Lin_exp_diff_neg),
	le_print_int(Lin_exp_diff_neg,Exp_diff_neg_int,Exp_diff_denominator),
	nad_maximize([Exp_diff_neg_int=Exp_diff_denominator*D|Cs],[D],[Delta]),
	greater_fr(Delta,0),!,
	cstr_get_it_name(Loop,Loop_name),
	check_loops_max(Loops,Head,Call,Lin_exp,Resets,Additions).
	
%add a variable
check_loops_max([Loop|Loops],Head,Call,Lin_exp,Resets,[Aux_name|Additions]):-
	loop_ph(Head,(Loop,_),Call,Cs,_,_),
	get_difference_version(Head,Call,Lin_exp,Lin_exp_diff),
	negate_le(Lin_exp_diff,Lin_exp_diff_neg),
	term_variables(Head,Vars_head),from_list_sl(Vars_head,Vars_head_set),
	term_variables(Lin_exp_diff_neg,Vars_exp),from_list_sl(Vars_exp,Vars_exp_set),
	difference_sl(Vars_head_set,Vars_exp_set,Vars_of_Interest),
	max_min_linear_expression_all(Lin_exp_diff_neg, Vars_of_Interest, Cs,max, Maxs),
	Maxs\=[],!,
	cstr_name_aux_var(Aux_name),
	maplist(cstr_generate_top_exp([Aux_name],ub),Maxs,Maxsums),
	save_pending_list(maxsum,Head,Call,Loop,Maxsums),
	check_loops_max(Loops,Head,Call,Lin_exp,Resets,Additions).		
		
%reset			
check_loops_max([Loop|Loops],Head,Call,Lin_exp,[Aux_name|Resets],Additions):-
	loop_ph(Head,(Loop,_),Call,Cs,_,_),
	copy_term((Head,Lin_exp),(Call,Lin_exp_p)),
	term_variables(Head,Vars_head),from_list_sl(Vars_head,Vars_head_set),
	term_variables(Lin_exp,Vars_exp),from_list_sl(Vars_exp,Vars_exp_set),
	difference_sl(Vars_head_set,Vars_exp_set,Vars_of_Interest),
	max_min_linear_expression_all(Lin_exp_p, Vars_of_Interest, Cs,max, Maxs),
	Maxs\=[],!,
	cstr_name_aux_var(Aux_name),
	maplist(cstr_generate_top_exp([Aux_name],ub),Maxs,Maxsums),
	save_pending_list(maxsum,Head,Call,Loop,Maxsums),
	check_loops_max(Loops,Head,Call,Lin_exp,Resets,Additions).	

	

generate_index([],Index_accum,[],Index_accum).
generate_index([Name|Names],Index_accum,[Var|Vars],Index):-
		generate_index(Names,[(Name,Var)|Index_accum],Vars,Index).
put_inside_mult(Factor,mult([Factor])).
		
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
:-dynamic pending/4.
:-dynamic new_phase_top/4.
:-dynamic new_phase_aux/4.

save_new_phase_top(Head,Call,Phase,Top):-
	assert(new_phase_top(Head,Call,Phase,Top)).
save_new_phase_aux(Head,Call,Phase,Top):-
	assert(new_phase_aux(Head,Call,Phase,Top)).
	
collect_phase_results(Head,Call,Phase,Tops_max,Tops_min,Auxs):-
	bagof_no_fail(Top,(new_phase_top(Head,Call,Phase,Top)),Tops),
	partition(is_ub_top,Tops,Tops_max,Tops_min),
	bagof_no_fail(Aux,(new_phase_aux(Head,Call,Phase,Aux)),Auxs),
	retractall(new_phase_top(_,_,_,_)),
	retractall(new_phase_aux(_,_,_,_)).
	
is_ub_top(bound(ub,_,_)).

save_pending_list(Max_min,Head,Call,Max_top):-
	maplist(save_pending(Max_min,Head,Call),Max_top).

save_pending_list(Max_min_sum,Head,Call,Loop,Max_top):-
	Type=..[Max_min_sum,Loop],
	maplist(save_pending(Type,Head,Call),Max_top).
	
save_pending(Max_min,Head,Call,Max_top):-
	assert(pending(Max_min,Head,Call,Max_top)).	

rf_limit(N):-
	get_param(n_rankings,[N]).
	
get_difference_version(Head,Call,Rf,Rf_diff):-
	copy_term((Head,Rf),(Call,Rfp)),
	subtract_le(Rf,Rfp,Rf_diff).		
	
le_print_int(Lin_exp,Exp,Den):-
		integrate_le(Lin_exp,Den,Lin_exp_nat),
		write_le(Lin_exp_nat,Exp).
	
get_ranking_functions_constraints(Max,Head,Call,Phase,Chain,Top):-
		bagof_no_fail(Rf,
	ranking_function(Head,Chain,Phase,Rf)
	   ,Rfs),
	   ut_split_at_pos(Rfs,Max,Rfs_selected,_),
	   maplist(get_difference_version(Head,Call),Rfs_selected,Rfs_diff),
	   maplist(cstr_get_it_name,Phase,Bounded),
	   append(Rfs_selected,Rfs_diff,Rfs_total),
	   maplist(cstr_generate_top_exp(Bounded,ub),Rfs_total,Top).
	   
get_ranking_functions_lower_constraints(Max,Head,Call,Phase,Chain,Top):-
		bagof_no_fail(Df,
			get_lower_bound_val(Head,Call,Chain,Phase,Df)
	   ,Dfs),
	   ut_split_at_pos(Dfs,Max,Dfs_selected,_),
	   maplist(cstr_get_it_name,Phase,Bounded),
	   maplist(cstr_generate_top_exp(Bounded,lb),Dfs_selected,Top).
	   
get_lower_bound_val(Head,Call,Chain,Phase,LB):-
	ranking_function(Head,Chain,Phase,Rf),
	copy_term((Head,Rf),(Call,Rf1)),
	subtract_le(Rf,Rf1,Rf_diff),
	integrate_le(Rf_diff,Den,Rf_diff_nat),
	write_le(Rf_diff_nat,Rf_diff_nat_print),
	phase_loop(Phase,_,Head,Call,Phi),
	Constraint= (Den* D = Rf_diff_nat_print),

	Cs_1 = [ Constraint | Phi],
	nad_maximize(Cs_1,[D],[Delta]),
	inverse_fr(Delta,Delta_inv),
	multiply_le(Rf_diff,Delta_inv,LB).	
	
is_difference(Head,Call,Lin_exp,Loop,Diff_list):-
	loop_ph(Head,(Loop,_),Call,Cs,_,_),
	
%FIXME check positivity
	%le_print_int(Lin_exp,Exp,_Den),
%	term_variables((Head,Call),Vars),
	%(nad_entails(Vars,Cs,[Exp>=0])->fail;true),
	
	difference_constraint2_farkas_dmatrix(Head,Call,Cs,Lin_exp,Diff_list),
	copy_term((Head,Call,Diff_list,Lin_exp),(Head2,Call2,Diff_list2,Lin_exp2)),
	maplist(write_le,Diff_list2,Diff_list_print),
	write_le(Lin_exp2,Lin_exp_print),
	numbervars((Head2,Call2),0,_),
	writeln((Lin_exp_print,Head2,Call2,Diff_list_print)).	
	
% provisional code		
max_min_top_expression_in_phase(Head,Call,Phase,bound(Op,Lin_exp,Bounded),Top_exps_new):-
	phase_transitive_closure(Phase,_,Head_total,Head,Cs_star_trans),
	phase_loop(Phase,_,Head,Call,Cs),
	ut_flat_list([Cs_star_trans,Cs],Context),
	term_variables(Head_total,Vars_of_Interest),
	(Op=ub->
	max_min_linear_expression_all(Lin_exp, Vars_of_Interest, Context,max, Maxs_out)
	;
	max_min_linear_expression_all(Lin_exp, Vars_of_Interest, Context,min, Maxs_out)
	),
	Head_total=Head,
	maplist(cstr_generate_top_exp(Bounded,Op),Maxs_out,Top_exps_new).			