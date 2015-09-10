/** <module> constraints_maximization

This module implements algorithms to maximize sets of constraints 
according to a polyhedron describing the relations between variables.
The module includes predicates to compress sets of constraints
 at the same time they are maximized. 
 
It is used in the cost_equation_solver.pl, the phase_solver.pl
 and the chain_solver.pl.

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

:- module(old_constraints_maximization,[
				  old_max_min_costs_in_phase/6]).
				  
:- use_module('../IO/params',[get_param/2]).
:- use_module('../db',[loop_ph/6,phase_loop/5]).
:- use_module('../utils/cofloco_utils',[
	        zip_with_op/4,
			tuple/3,
			sort_with/3,
			bagof_no_fail/3,
			repeat_n_times/3,
			normalize_constraint/2,
			normalize_constraint_wrt_var/3,	
			normalize_constraint_wrt_vars/3,	    
			write_sum/2]).
:- use_module('../ranking_functions',[
				      ranking_function/4,
				      partial_ranking_function/7]).	
				      		
:-use_module('../refinement/invariants',[backward_invariant/4,
			      phase_transitive_closure/5,
			      get_phase_star/4,
			      forward_invariant/4]).			
:- use_module('../utils/polyhedra_optimizations',[nad_entails_aux/3,
			slice_relevant_constraints_and_vars/5,nad_project_group/3,
			nad_consistent_constraints_group/2]).			

:- use_module('../utils/cost_expressions',[cexpr_maximize/4,
			get_le_without_constant/3,
			cexpr_substitute_lin_exp_by_vars/4,
			normalize_le/2,
			is_linear_exp/1]).
:- use_module('../utils/cost_structures',[
			cstr_extract_top_maxs/3,
		    cstr_extract_top_mins/3,
			cstr_remove_cycles/2,
			cstr_name_aux_var/1,
			cstr_get_it_name/2,
			cstr_propagate_summatory/4,
			cstr_generate_top_exp/4,
			cstr_generate_top_exp_inv/4,
			cstr_empty/1,
			cstr_get_lin_exp_from_tops/3,
			cstr_join/3]).			
:-use_module('../utils/template_inference',[
	difference_constraint2_farkas_dmatrix/5
	]).			
:- use_module(constraints_generation,[add_phase_upper_bounds/6,add_phase_lower_bounds/6]).			
:- use_module(stdlib(counters),[counter_increase/3]).

:- use_module(stdlib(utils),[ut_flat_list/2,ut_split_at_pos/4]).
:- use_module(stdlib(set_list)).
:- use_module(stdlib(list_map)).
:- use_module(stdlib(multimap)).
:- use_module(stdlib(numeric_abstract_domains),[nad_maximize/3,nad_minimize/3,
						nad_list_lub/2,
						nad_project/3,nad_entails/3,nad_normalize/2,
						nad_consistent_constraints/1]).
:- use_module(stdlib(linear_expression),[is_constant_le/1,
	integrate_le/3,
	write_le/2,
	multiply_le/3,
	parse_le_fast/2,
	elements_le/2,
	subtract_le/3,
	negate_le/2,
	constant_le/2]).							
:- use_module(stdlib(fraction),[greater_fr/2,geq_fr/2,negate_fr/2,multiply_fr/3,min_fr/3,max_fr/3,negate_fr/2,inverse_fr/2]).
:- use_module(stdlib(fraction_list),[max_frl/2,min_frl/2]).





old_max_min_costs_in_phase(Costs,Head,Call,Forward_inv,Phase,Cost_final):-
	add_phase_upper_bounds(Head,Call,Phase,_,Top_exps_new,Aux_exps_new),
	add_phase_lower_bounds(Head,Call,Phase,_,LTop_exps_new,LAux_exps_new),

	maplist(cstr_remove_cycles,Costs,Costs_simple),
	maplist(cstr_propagate_summatory,Phase,Costs_simple,Costs_propagated,Summatories_pairs),
	maplist(tuple,Summatories,LSummatories,Summatories_pairs),
	maplist(max_min_top_expressions_in_loop(Head,Call,Phase,Forward_inv),Phase,Costs_propagated,Costs_maximized),
	compute_summatories(Head,Call,Phase,max,Forward_inv,Summatories,Top_exps2,Aux_exps2),
	compute_summatories(Head,Call,Phase,min,Forward_inv,LSummatories,LTop_exps2,LAux_exps2),
	cstr_empty(Empty_cost),
	foldl(cstr_join,Costs_maximized,Empty_cost,cost(Top_exps,LTop_exps,Aux_exps,Bases,Base)),
	ut_flat_list([Top_exps_new,Top_exps2,Top_exps],Top_exps_final),
	ut_flat_list([Aux_exps_new,Aux_exps2,LAux_exps_new,LAux_exps2,Aux_exps],Aux_exps_final),
	ut_flat_list([LTop_exps_new,LTop_exps2,LTop_exps],LTop_exps_final),
	cstr_remove_cycles(cost(Top_exps_final,LTop_exps_final,Aux_exps_final,Bases,Base),Cost_final).	
	
max_min_top_expressions_in_loop(Head,Call,Phase,Forward_inv,Loop,cost(Top_exps,LTop_exps,Aux,Bs,B),cost(Top_exps_new2,LTop_exps_new2,Aux2,Bs,B)):-
	maplist(max_min_top_expression_in_loop(Head,Call,Phase,Forward_inv,Loop),Top_exps,Top_exps_new,Aux_exps_new),
	maplist(max_min_top_expression_in_loop(Head,Call,Phase,Forward_inv,Loop),LTop_exps,LTop_exps_new,LAux_exps_new),
	ut_flat_list(Top_exps_new,Top_exps_new2),
	ut_flat_list(LTop_exps_new,LTop_exps_new2),
	ut_flat_list([Aux_exps_new,LAux_exps_new,Aux],Aux2).


max_min_top_expression_in_loop(Head,Call,Phase,Forward_inv,Loop,bound(Op,Lin_exp,Bounded),Top_exps_new,[]):-
	%get_phase_star(Head_total,Head,Phase,Cs_star_trans),
	phase_transitive_closure(Phase,_,Head_total,Head,Cs_star_trans),
	loop_ph(Head,(Loop,_),Call,Cs,_,_),
	ut_flat_list([Cs_star_trans,Cs,Forward_inv],Context),
	term_variables(Head_total,Vars_of_Interest),
	(Op=ub->
	max_min_linear_expression_all(Lin_exp, Vars_of_Interest, Context,max, Maxs_out)
	;
	max_min_linear_expression_all(Lin_exp, Vars_of_Interest, Context,min, Maxs_out)
	),
	Head_total=Head,
	maplist(cstr_generate_top_exp(Bounded,Op),Maxs_out,Top_exps_new).


compute_summatories(Head,Call,Phase,_Max_min,Forward_inv,Summatories,Top_exps2,Aux_exps2):-
	maplist(get_difference_norms(Head,Call),Summatories,Phase,Summatories_non_diff,Summatories_diff),
	compress_differences(Head,Call,Phase,Summatories_diff,Top1,Aux1,Summatories_left1),
	compress_triangles(Head,Call,Summatories_non_diff,Top2,Aux2,Summatories_left2),
	maplist(append,Summatories_left1,Summatories_left2,Summatories_left),
	
	maplist(simple_multiplication_list(Head,Call,Phase,Forward_inv),Phase,Summatories_left,Tops,Auxs),
	ut_flat_list([Top1,Top2,Tops],Top_exps2),
	ut_flat_list([Aux1,Aux2,Auxs],Aux_exps2).

get_difference_norms(_Head,_,[],_Loop,[],[]).
get_difference_norms(Head,Call,[bound(Op,Lin_exp,Bounded)|Tops],Loop,Summ_non_diff,Summ_diff2):-
	is_difference(Head,Call,Lin_exp,Loop,Exp_diff_list),!,
	maplist(cstr_generate_top_exp(Bounded,Op),Exp_diff_list,New_diffs),
	get_difference_norms(Head,Call,Tops,Loop,Summ_non_diff,Summ_diff),
	append(New_diffs,Summ_diff,Summ_diff2).
get_difference_norms(Head,Call,[bound(Op,Lin_exp,Bounded)|Tops],Loop,[bound(Op,Lin_exp,Bounded)|Summ_non_diff],Summ_diff):-
	get_difference_norms(Head,Call,Tops,Loop,Summ_non_diff,Summ_diff).	

is_difference(Head,Call,Lin_exp,Loop,Diff_list):-
	loop_ph(Head,(Loop,_),Call,Cs,_,_),
	le_print_int(Lin_exp,Exp,_Den),
	term_variables((Head,Call),Vars),
	%(nad_entails(Vars,Cs,[Exp>=0])->fail;true),
	
	difference_constraint2_farkas_dmatrix(Head,Call,Cs,Lin_exp,Diff_list),
	copy_term((Head,Call,Diff_list,Lin_exp),(Head2,Call2,Diff_list2,Lin_exp2)),
	maplist(write_le,Diff_list2,Diff_list_print),
	write_le(Lin_exp2,Lin_exp_print),
	numbervars((Head2,Call2),0,_),
	writeln((Lin_exp_print,Head2,Call2,Diff_list_print)).
	

compress_differences(Head,Call,Phase,Summatories,Top,Aux,Summatories_left):-
	maplist(cstr_get_lin_exp_from_tops(Op),Summatories,Expressions_sets),
	(Op=ub->Max_min=max;Max_min=min),
	unions_sl(Expressions_sets,All_expressions),	
	maplist(get_expressions_map(Expressions_sets,Phase),All_expressions,Expressions_map),
	maplist(tuple,All_expressions,_Solutions,Pairs),
	maplist(tuple,Pairs,Expressions_map,Pairs1),
	include(try_inductive_compression(Head,Phase,Call,Max_min),Pairs1,Summed),
	maplist(tuple,Summed_map,_,Summed),
	generate_top_and_aux_from_compressed(Summed_map,Summatories,Top,Aux,Summatories_left).

compress_triangles(_Head,_Call,Summatories,[],[],Summatories).


get_expressions_map(Ex_sets,Phase,Lin_exp,Map_set):-
	maplist(loop_contains_exp(Lin_exp),Ex_sets,Phase,Map),
	ut_flat_list(Map,Map_flat),
	from_list_sl(Map_flat,Map_set).
	
loop_contains_exp(Lin_exp,Set,Loop,[Loop]):-
		contains_sl(Set,Lin_exp),!.

loop_contains_exp(_Lin_exp,_Set,_Loop,[]).	


generate_top_and_aux_from_compressed([],Summatories,[],[],Summatories).
generate_top_and_aux_from_compressed([(Exp,(Bounded,Top1,Aux1))|Compressed_norms],Summatories,Top,Aux,Summatories_left):-
		remove_tops_with_exp(Summatories,[],Exp,Bounded,Summatories1),
		generate_top_and_aux_from_compressed(Compressed_norms,Summatories1,Top2,Aux2,Summatories_left),
		append(Top1,Top2,Top),
		append(Aux1,Aux2,Aux).
		
remove_tops_with_exp([],Bounded,_Exp,Bounded,[]).
remove_tops_with_exp([Summ|Summatories],Bounded_accum,Exp,Bounded,[Summ1|Summatories1]):-
	remove_tops_with_exp_1(Exp,Summ,Summ1,Bounded_aux),
	append(Bounded_aux,Bounded_accum,Bounded_accum1),
	remove_tops_with_exp(Summatories,Bounded_accum1,Exp,Bounded,Summatories1).
	
	
remove_tops_with_exp_1(Lin_exp,Tops,Tops1,Bounded):-
	partition(top_has_exp(Lin_exp),Tops,Tops_selected,Tops1),
	(
	Tops_selected=[bound(_,_,Bounded)]
	;
	(Tops_selected=[],Bounded=[])
	),!.
remove_tops_with_exp_1(_Lin_exp,Tops,_Tops1,_Bounded):-
	throw(implementation_error('failed assumption that a linear expression appears only once after substitution',Tops)).
	


top_has_exp(Lin_exp,bound(_Op,Lin_exp2,_)):-Lin_exp==Lin_exp2.

try_inductive_compression(Head,Phase,Call,Max_Min,((L,(Bounded_var,Tops,Auxs)),Expressions_map)):-
	L=Coeffs+Delta,
	L_wc=Coeffs+0,
	difference_sl(Phase,Expressions_map,Other_loops),
	(Max_Min=max->	
 	(greater_fr(Delta,0)->
 		maplist(generate_loop_info(Delta,max),Expressions_map,Same_loops_info)
    	;
    	Same_loops_info=[]
    	)
	;
    geq_fr(Delta,0),
    Same_loops_info=[]
	),
	maplist(is_not_negative(Head,Call,L_wc),Expressions_map),
	maplist(check_bad_loops(Head,Call,L_wc,Max_Min),Other_loops,Bad_loops_info),
	ut_flat_list([Same_loops_info,Bad_loops_info],Bad_loops_info_flat),!,	
	generate_top_and_aux(Bad_loops_info_flat,Max_Min,[L_wc],Bounded_var,Tops,Auxs).
	
	
%TODO stop excluding mins
generate_top_and_aux(Info,Max_min,Maxs,Bounded,Tops,Auxs):-
	(Max_min=max-> Op=ub;Op=lb),
	%we can always exclude min
	exclude(is_min,Info,Info2),
	(Info2=[]->
	maplist(cstr_generate_top_exp(Bounded,Op),Maxs,Tops),
	Auxs=[]
	;
	maplist(get_factors_from_loop_info,Info2,Factors,Index),
	cstr_name_aux_var(Name_aux),
	Internal_exp=exp([(Name_aux,Var_aux)|Index],[],add([mult([Var_aux])|Factors]),add([])),
	Auxs=[bound(Op,Internal_exp,Bounded)],
	maplist(cstr_generate_top_exp([Name_aux],Op),Maxs,Tops)
	).

is_min(	(min(_),_)).
	
get_factors_from_loop_info((max(Loop),1),mult([Var_aux]),(Loop_name,Var_aux)):-
	cstr_get_it_name(Loop,Loop_name),!.
get_factors_from_loop_info((max(Loop),N),mult([Var_aux,N]),(Loop_name,Var_aux)):-
	cstr_get_it_name(Loop,Loop_name).


get_loop_cs(Head,Call,Loop,Cs):-
	loop_ph(Head,(Loop,_),Call,Cs,_,_).

generate_loop_info(Delta,Max_min,Loop,(Max_min_loop,Delta)):-
	Max_min_loop=..[Max_min,Loop].

is_not_negative(Head,Call,Lin_exp,Loop):-
	loop_ph(Head,(Loop,_),Call,Cs,_,_),
	integrate_le(Lin_exp,_,Lin_exp_nat),
	write_le(Lin_exp_nat,Expression_nat),
	term_variables(Cs,Vars_constraint),
	nad_entails(Vars_constraint,Cs,[Expression_nat>=0]).


check_bad_loops(Head,Call,Lin_exp,Max_Min,Loop,Info):-
	loop_ph(Head,(Loop,_),Call,Cs,_,_),
	elements_le(Lin_exp,Vars_exp_set),
	term_variables(Call,Vars_call),from_list_sl(Vars_call,Vars_call_set),
	(intersection_sl(Vars_exp_set,Vars_call_set,[])->
		copy_term((Lin_exp,Head),(Lin_exp_p,Call)),
		subtract_le(Lin_exp,Lin_exp_p,Lin_exp_diff),
		integrate_le(Lin_exp_diff,Den,Lin_exp_diff_nat),
		write_le(Lin_exp_diff_nat,Exp_diff),
		Constraint= (Den*D=Exp_diff)
		
		;
		integrate_le(Lin_exp,Den,Lin_exp_nat),
		write_le(Lin_exp_nat,Exp),
		Constraint= (Den*D=Exp)
	),
	Cs_1 = [ Constraint | Cs],
	(Max_Min=max->
	  (nad_minimize(Cs_1,[D],[Delta])->
	  Pos_loop=max(Loop),
	  Neg_loop=min(Loop)
	  ;
	%  term_variables(Head,Vars),
	%  max_min_linear_expression_all(Exp,Vars,Cs,min, MINS),
	  fail
	  )
	;
	  nad_maximize(Cs_1,[D],[Delta]),
	  Pos_loop=min(Loop),
	  Neg_loop=max(Loop)
	),
	negate_fr(Delta,Constant),
	(geq_fr(Constant,0)->
	   (Constant\==0 ->
	   	  Info=(Pos_loop,Constant)
	 	;
	   	  Info=[]
	   )
	 ;
	 Info=(Neg_loop,Constant)
	 ).


simple_multiplication_list(Head,Call,Phase,Forward_inv,Loop,Sums,Tops,Auxs):-
	maplist(simple_multiplication(Head,Call,Phase,Forward_inv,Loop),Sums,Tops,Auxs).
	
simple_multiplication(Head,Call,Phase,Forward_inv,Loop,bound(Op,Exp,Bounded),Top_exps_new,Aux_exps_total):-
	cstr_name_aux_var(Aux_name),
	max_min_top_expression_in_loop(Head,Call,Phase,Forward_inv,Loop,bound(Op,Exp,[Aux_name]),Top_exps_new,Aux_exps_new),
	cstr_get_it_name(Loop,Loop_name),
	Internal_exp=exp([(Aux_name,Aux_var),(Loop_name,It_var)],[],add([mult([It_var,Aux_var])]),add([])),
    Aux_exp=bound(Op,Internal_exp,Bounded),
    append(Aux_exps_new,[Aux_exp],Aux_exps_total).

/*
%triangular
try_inductive_compression(Head,Phase,Forward_inv,_Cs_star_trans,Call,Max_Min,((L2,(Bounded_var,Tops,Auxs)),Expressions_map)):-
	%phase_loop(Phase,_,Call,Call2,Phi),
	%trace,
	term_variables(L2,Vars_L),
	Vars_L\=[],
	Head=..[_|EVars],
	
%	from_list_sl(EVars,EVars_set),
%	difference_sl(Vars_l_set,EVars_set,[]),%only entry variables
	
	(Expressions_map=Phase->
		phase_loop(Phase,_,Head,Call,Phi)
		;
		maplist(get_loop_cs(Head,Call),Expressions_map,Css),
		nad_list_lub(Css,Phi)
	),
	max_min_linear_expression_all(L2,EVars,Phi,Max_Min,Lss),
	member(L,Lss),\+term_variables(L,[]),
	
	difference_sl(Phase,Expressions_map,Other_loops),

	copy_term((Head,L),(Call,Lp)),
	

	ut_flat_list([Phi,Forward_inv],Cs_comb),
	%term_variables(Cs_comb,Vars_constraint),
	%trace,
	normalize_constraint( D=(Lp-L) ,Inductive_constraint_aux),
	(Max_Min=max->	
    nad_maximize([Inductive_constraint_aux|Cs_comb],[D],[Delta])
    ,
    Delta\=0/1
	;
    nad_minimize([Inductive_constraint_aux|Cs_comb],[D],[Delta])
    ,
    Delta\=0/1
	),
	maplist(is_not_negative(Head,Call,L),Expressions_map),
	maplist(check_bad_loops(Head,Call,Forward_inv,L,Max_Min),Other_loops,Bad_loops_info),
	ut_flat_list(Bad_loops_info,Bad_loops_info_flat),
fail,
	generate_top_and_aux_triangular(Delta,Expressions_map,Bad_loops_info_flat,Max_Min,Lss,Bounded_var,Tops,Auxs).
	


generate_top_and_aux_triangular(Delta,[Loop],Info,Max_min,Maxs,Bounded,Tops,Auxs):-
	(Max_min=max-> Op=ub;Op=lb),
	multiply_fr(Delta,1/2,Delta_2),
	%we can always exclude min
	exclude(is_min,Info,Info2),
	maplist(get_factors_from_loop_info,Info2,Factors,Index),
	cstr_name_aux_var(Name_aux),
	cstr_get_it_name(Loop,Name_loop),
	(greater_fr(Delta,0)->
	Exp=exp([(Name_aux,Var_aux),(Name_loop,Var_loop_1),(Name_loop,Var_loop_2),(Name_loop,Var_loop_3),(Name_loop,Var_loop_4)|Index],
	[],
	add([mult([Var_loop_1,Var_aux]),mult([Var_loop_2,Var_loop_3,Delta_2]),mult([Var_loop_4,Delta_2])|Factors]),
	add([]))
	;
	negate_fr(Delta_2,Delta_3),
	Exp=exp([(Name_aux,Var_aux),(Name_loop,Var_loop_1)|Index],
	[(Name_loop,Var_loop_2),(Name_loop,Var_loop_3),(Name_loop,Var_loop_4)],
	add([mult([Var_loop_1,Var_aux])|Factors]),
	add([mult([Var_loop_2,Var_loop_3,Delta_3]),mult([Var_loop_4,Delta_3])]))
	),
	Auxs=[bound(Op,Exp,Bounded)],
	maplist(cstr_generate_top_exp([Name_aux],Op),Maxs,Tops).	

*/