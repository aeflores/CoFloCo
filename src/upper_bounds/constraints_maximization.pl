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

:- module(constraints_maximization,[
				  max_min_constrs_in_cost_equation/6,
				  max_min_top_exprs_in_chain/6,
				  max_min_costs_in_phase/5,
				  max_min_linear_expression_all/5]).
				  
:- use_module('../IO/params',[get_param/2]).
:- use_module('../db',[loop_ph/6,phase_loop/5]).
:- use_module('../utils/cofloco_utils',[
	        zip_with_op/4,
			tuple/3,
			sort_with/3,
			repeat_n_times/3,
			normalize_constraint/2,
			normalize_constraint_wrt_var/3,	
			normalize_constraint_wrt_vars/3,	    
			write_sum/2]).
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
			cstr_remove_cycles/2,
			cstr_name_aux_var/1,
			cstr_get_it_name/2,
			cstr_propagate_summatory/4,
			cstr_generate_top_exp/3,
			cstr_empty/1,
			cstr_join/3]).			
			
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
:- use_module(stdlib(fraction),[greater_fr/2,geq_fr/2,negate_fr/2]).
:- use_module(stdlib(fraction_list),[max_frl/2,min_frl/2]).
				
%/*										
max_min_constrs_in_cost_equation((Top_exps_list,Aux_lists),Max_min,_Base_calls,Phi,TVars,(New_top_exps,Aux_lists_flat)):-
	ut_flat_list(Aux_lists,Aux_lists_flat),
	ut_flat_list(Top_exps_list,Top_exps),
	generate_constraints(Top_exps,Max_min,[],Constraints,Dicc),
	maplist(tuple,_Names_set,Extra_vars,Dicc),
	from_list_sl(Extra_vars,Extra_vars_set),
	foldl(inverse_map,Dicc,[],Dicc_inv),
	append(Constraints,Phi,Phi1),
	append(Extra_vars,TVars,Total_vars),
	nad_project(Total_vars,Phi1,Projected),
	cstr_generate_top_expr_from_poly(Projected,Max_min,Dicc_inv,Extra_vars_set,New_top_exps),!.
%*/

/*
maximize_top_expressions_in_cost_equation(Top_exps_list,Base_call_vars,Phi,TVars,New_tops,New_auxs):-
	from_list_sl(TVars,TVars_set),
	unions_sl([TVars_set|Base_call_vars],All_vars),
	incremental_maximization_cost_equation(Top_exps_list,Base_call_vars,carry_info([],[]),All_vars,Phi,New_tops,New_auxs).

incremental_maximization_cost_equation([],[],carry_info(Dicc_inv,Extra_vars_set),_Vars,Phi,New_top_exps,[]):-
	cstr_generate_top_expr_from_poly(Phi,Dicc_inv,Extra_vars_set,New_top_exps).

incremental_maximization_cost_equation([Top_exps|Top_exp_list],[Base_vars|Base_vars_list],
										Carry_info,Vars,Phi,New_top_exps,[]):-
	Carry_info=carry_info(Dicc_inv,Extra_vars_set),
	generate_constraints(Top_exps,[],Constraints,Dicc1),
	maplist(tuple,_Names_set1,Extra_vars1,Dicc1),
	from_list_sl(Extra_vars1,Extra_vars_set1),
	foldl(inverse_map,Dicc1,[],Dicc_inv1),
	append(Constraints,Phi,Phi1),
	difference_sl(Vars,Base_vars,Vars1),
	unions_sl([Extra_vars_set1,Extra_vars_set,Vars1],Total_vars),
	nad_project(Total_vars,Phi1,Projected),
	check_lost_bounds(Projected,Extra_vars_set,Lost_vars),
	(Lost_vars\=[]->
		throw(lost_expressions),
		%get_needed_expressions(Lost_vars,Phi,Base_vars,Expressions),
		writeln(lost_expressions(Lost_vars,Dicc_inv))
	;
		true
		),
	update_carry_info(Carry_info,Extra_vars_set1,Dicc_inv1,Carry_info1),
	incremental_maximization_cost_equation(Top_exp_list,Base_vars_list,Carry_info1,Vars1,Projected,New_top_exps,[]).

update_carry_info(carry_info(Dicc,Var_set),Var_set1,Dicc1,carry_info(Dicc2,Var_set2)):-
	union_sl(Var_set,Var_set1,Var_set2),
	join_lm(Dicc,Dicc1,Dicc2).

check_lost_bounds([],Lost_vars,Lost_vars):-!.
check_lost_bounds(_,[],[]):-!.
check_lost_bounds([C|Cs],Vars,Lost_vars):-
	normalize_constraint_wrt_vars(C,Vars,C1),!,
	(C1= (Its =< _Exp)->
		from_list_sl(Its,Its_set),
		difference_sl(Vars,Its_set,Vars1)
		;
		Vars1=Vars
	),
	check_lost_bounds(Cs,Vars1,Lost_vars).
	
check_lost_bounds([_C|Cs],Vars,Lost_vars):-
	check_lost_bounds(Cs,Vars,Lost_vars).
*/
	
max_min_top_exprs_in_chain(Top_exps,Max_min,_,Phi,Head,(New_top_exps,[])):-	
	term_variables(Head,TVars),
	generate_constraints(Top_exps,Max_min,[],Constraints,Dicc),
	maplist(tuple,_Names,Extra_vars,Dicc),
	from_list_sl(Extra_vars,Extra_vars_set),
	foldl(inverse_map,Dicc,[],Dicc_inv),
	append(Constraints,Phi,Phi1),
	append(Extra_vars,TVars,Total_vars),
	nad_project(Total_vars,Phi1,Projected),
	
%	check_lost_bounds(Projected,Extra_vars_set,Lost_vars),
%	(Lost_vars\=[]->
%		throw(lost_expressions),
%		%get_needed_expressions(Lost_vars,Phi,Base_vars,Expressions),
%		writeln(lost_expressions(Lost_vars,Dicc_inv))
%	;
%		true
%		),
	cstr_generate_top_expr_from_poly(Projected,Max_min,Dicc_inv,Extra_vars_set,New_top_exps).
	
	
max_min_costs_in_phase(Costs,Head,Call,Phase,Cost_final):-
	add_phase_upper_bounds(Head,Call,Phase,_,Top_exps_new,Aux_exps_new),
	add_phase_lower_bounds(Head,Call,Phase,_,LTop_exps_new,LAux_exps_new),
	
	maplist(cstr_remove_cycles,Costs,Costs_simple),
	maplist(cstr_propagate_summatory,Phase,Costs_simple,Costs_propagated,Summatories_pairs),
	maplist(tuple,Summatories,LSummatories,Summatories_pairs),
	maplist(max_min_top_expressions_in_loop(Head,Call,Phase),Phase,Costs_propagated,Costs_maximized),
	compute_summatories(Head,Call,Phase,max,Summatories,Top_exps2,Aux_exps2),
	compute_summatories(Head,Call,Phase,min,LSummatories,LTop_exps2,LAux_exps2),
	cstr_empty(Empty_cost),
	foldl(cstr_join,Costs_maximized,Empty_cost,cost(Ub_constrs,Lb_constrs,Bases,Base)),
	Ub_constrs=(Top_exps,Aux_exps),
	ut_flat_list([Top_exps_new,Top_exps2,Top_exps],Top_exps_final),
	ut_flat_list([Aux_exps_new,Aux_exps2,Aux_exps],Aux_exps_final),
	
	Lb_constrs=(LTop_exps,LAux_exps),
	ut_flat_list([LTop_exps_new,LTop_exps2,LTop_exps],LTop_exps_final),
	ut_flat_list([LAux_exps_new,LAux_exps2,LAux_exps],LAux_exps_final),
	cstr_remove_cycles(cost((Top_exps_final,Aux_exps_final),(LTop_exps_final,LAux_exps_final),Bases,Base),Cost_final).
		
	
compute_summatories(Head,Call,Phase,Max_min,Summatories,Top_exps2,Aux_exps2):-
	compute_sums(Head,Call,Phase,Max_min,Summatories,Top,Aux,Summatories_left),
	maplist(simple_multiplication_list(Head,Call,Phase,Max_min),Phase,Summatories_left,Tops,Auxs),
	ut_flat_list([Top,Tops],Top_exps2),
	ut_flat_list([Aux,Auxs],Aux_exps2).


simple_multiplication_list(Head,Call,Phase,Max_min,Loop,Sums,Tops,Auxs):-
	maplist(simple_multiplication(Head,Call,Phase,Max_min,Loop),Sums,Tops,Auxs).
	
simple_multiplication(Head,Call,Phase,Max_min,Loop,bound(Exp,Bounded),Top_exps_new,Aux_exps_total):-
	cstr_name_aux_var(Aux_name),
	max_min_top_expression_in_loop(Head,Call,Phase,Max_min,Loop,bound(Exp,[Aux_name]),Top_exps_new,Aux_exps_new),
	cstr_get_it_name(Loop,Loop_name),
    Aux_exp=bound([(Aux_name,Aux_var),(Loop_name,It_var)],add([mult([It_var,Aux_var])]),Bounded),
    append(Aux_exps_new,[Aux_exp],Aux_exps_total).

	
max_min_top_expressions_in_loop(Head,Call,Phase,Loop,cost((Top_exps,Aux),(LTop_exps,LAux),Bs,B),cost((Top_exps_new2,Aux2),(LTop_exps_new2,LAux2),Bs,B)):-
	maplist(max_min_top_expression_in_loop(Head,Call,Phase,max,Loop),Top_exps,Top_exps_new,Aux_exps_new),
	ut_flat_list(Top_exps_new,Top_exps_new2),
	ut_flat_list([Aux_exps_new|Aux],Aux2),
	
	maplist(max_min_top_expression_in_loop(Head,Call,Phase,min,Loop),LTop_exps,LTop_exps_new,LAux_exps_new),
	ut_flat_list(LTop_exps_new,LTop_exps_new2),
	ut_flat_list([LAux_exps_new|LAux],LAux2).

max_min_top_expression_in_loop(Head,Call,Phase,Max_min,Loop,bound(Exp,Bounded),Top_exps_new,Aux_exps_new):-
	traditional_phase_maximization(Head,Call,Phase,Max_min,Loop,Exp,Bounded,Top_exps_new,Aux_exps_new).
	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

traditional_phase_maximization(Head,Call,Phase,Max_min,Loop,Exp,Bounded,Top_exps_new,[]):-
	get_phase_star(Head_total,Head,Phase,Cs_star_trans),
	loop_ph(Head,(Loop,_),Call,Cs,_,_),
	ut_flat_list([Cs_star_trans,Cs],Context),
	term_variables(Head_total,Vars_of_Interest),
	max_min_linear_expression_all(Exp, Vars_of_Interest, Context,Max_min, Maxs_out),
	Head_total=Head,
	maplist(cstr_generate_top_exp(Bounded),Maxs_out,Top_exps_new).

compute_sums(Head,Call,Phase,Max_min,Summatories,Top,Aux,Summatories_left):-
	phase_transitive_closure(Phase,_,Head,Call,Cs_transitive),
	get_phase_star(Head,Call,Phase,Cs_star_trans),
	maplist(get_top_lin_expr,Summatories,Expressions_sets),
	unions_sl(Expressions_sets,All_expressions),	
	maplist(get_expressions_map(Expressions_sets,Phase),All_expressions,Expressions_map),
	maplist(tuple,All_expressions,_,Pairs),
	maplist(tuple,Pairs,Expressions_map,Pairs1),
	include(try_inductive_compression(Head,Phase,Cs_star_trans,Cs_transitive,Call,Max_min),Pairs1,Compressed_norms),
	maplist(tuple,Compressed_norms1,_,Compressed_norms),
	generate_top_and_aux_from_compressed(Compressed_norms1,Summatories,Top,Aux,Summatories_left).
	
%FIXME for lower bounds!!
generate_top_and_aux_from_compressed([],Summatories,[],[],Summatories).
generate_top_and_aux_from_compressed([(Exp,(Bad_loops_info,Maxs))|Compressed_norms],Summatories,Top,Aux,Summatories_left):-
		remove_one_instance(Summatories,Exp,Bounded,Summatories1),
		generate_top_and_aux(Bad_loops_info,Maxs,Bounded,Top1,Aux1),
		generate_top_and_aux_from_compressed(Compressed_norms,Summatories1,Top2,Aux2,Summatories_left),
		append(Top1,Top2,Top),
		append(Aux1,Aux2,Aux).
		
remove_one_instance([],_,[],[]).
remove_one_instance([Summatories|Summatories_list],Exp,Bounded2,[Summatories1|Summatories_list1]):-
	remove_one_instance_1(Summatories,Exp,Bounded,Summatories1),!,
	remove_one_instance(Summatories_list,Exp,Bounded1,Summatories_list1),
	append(Bounded,Bounded1,Bounded2).
	
remove_one_instance([Summatories|Summatories_list],Exp,Bounded,[Summatories|Summatories_list1]):-
	remove_one_instance(Summatories_list,Exp,Bounded,Summatories_list1).

remove_one_instance_1([bound(Exp,Bounded)|More],Exp1,Bounded,More):-
	Exp==Exp1,!.
remove_one_instance_1([Summ|More],Exp1,Bounded2,[Summ|More1]):-
			remove_one_instance_1(More,Exp1,Bounded2,More1).
			

generate_top_and_aux(Info,Maxs,Bounded,Tops,Aux):-
	exclude(is_min,Info,Info2),
	(Info2=[]->
	maplist(cstr_generate_top_exp(Bounded),Maxs,Tops),
	Aux=[]
	;
	maplist(get_factors_from_loop_info,Info2,Factors,Index),
	cstr_name_aux_var(Name_aux),
	Aux=[bound([(Name_aux,Var_aux)|Index],add([mult([Var_aux])|Factors]),Bounded)],
	maplist(cstr_generate_top_exp([Name_aux]),Maxs,Tops)
	).
	
get_factors_from_loop_info((max(Loop),1),mult([Var_aux]),(Loop_name,Var_aux)):-
	cstr_get_it_name(Loop,Loop_name),!.
get_factors_from_loop_info((max(Loop),N),mult([Var_aux,N]),(Loop_name,Var_aux)):-
	cstr_get_it_name(Loop,Loop_name).


is_min(	(min(_),_)).
		
get_top_lin_expr(Tops,Exps_set):-
 	maplist(get_expression_from_top,Tops,Exps),
 	from_list_sl(Exps,Exps_set).
get_expression_from_top(bound(Exp,_),Exp).
	
get_expressions_map(Ex_sets,Phase,Exp,Map_set):-
	maplist(loop_contains_exp(Exp),Ex_sets,Phase,Map),
	ut_flat_list(Map,Map_flat),
	from_list_sl(Map_flat,Map_set).
	
loop_contains_exp(Exp,Set,Loop,[Loop]):-
		contains_sl(Set,Exp),!.
loop_contains_exp(_Exp,_Set,_Loop,[]).		
	
get_loop_cs(Head,Call,Loop,Cs):-
	loop_ph(Head,(Loop,_),Call,Cs,_,_).
	

try_inductive_compression(Head,Phase,Cs_star_trans,Cs_trans,Call,Max_Min,((L,(Bad_loops_info_flat,[L|Maxs])),Expressions_map)):-
	%phase_loop(Phase,_,Call,Call2,Phi),
	Head=..[_|EVars],
	%trace,
	%(Expressions_map=[Loop]->
	%   loop_ph(Head,(Loop,_),Call,Phi,_,_)
	%   copy_term((loop_ph(Head,(Loop,_),Call,Phi,_,_),L),(Loop1,Lprint)),
	 %  numbervars(Loop1,0,_),
	%   writeln((Loop1,Lprint))
	%   ;
	   phase_loop(Phase,_,Head,Call,Phi),
	% ),
	difference_sl(Phase,Expressions_map,Bad_loops),
	copy_term((Head,Call,Phi,L),(Call,Call2,Cs2,L2)),
	copy_term((Head,Call,L),(Head,Call2,L_total)),
	

	ut_flat_list([Cs_trans,Cs2],Cs_comb),
    %ut_flat_list([Phi,Cs2],Cs_comb),
	%Call2=..[_|ECall3],
	%append(EVars,ECall3,Vars),

	term_variables(Cs_comb,Vars_constraint),
	%slice_relevant_constraints_and_vars(Vars_constraint,Vars,Cs_comb,Vars1,Cs_comb1),
	(Max_Min=max->	
	%normalize_constraint(L+L2=<L_total,Inductive_constraint),
	%nad_entails(Vars_constraint,Cs_comb,[Inductive_constraint]),	
	normalize_constraint( D=(L+L2-L_total) ,Inductive_constraint_aux),
    nad_maximize([Inductive_constraint_aux|Cs_comb],[D],[Delta]),
 	(greater_fr(Delta,0)->
 		maplist(generate_loop_info(Delta,max),Expressions_map,Same_loops_info)
    	;
    	Same_loops_info=[]
    	)
	;
	normalize_constraint(L+L2>=L_total,Inductive_constraint),
	nad_entails(Vars_constraint,Cs_comb,[Inductive_constraint])
	),
	maplist(does_not_decrease(Head,Call,L),Expressions_map),
%	(
	maplist(check_bad_loops(Head,Call,L,Max_Min),Bad_loops,Bad_loops_info)
%	->true;throw(missed_compression_opportunity))
	,
	%Bad_loops_info=[],
	ut_flat_list([Same_loops_info,Bad_loops_info],Bad_loops_info_flat),!,
	maplist(get_loop_cs(Call,Call2),Expressions_map,Css),
	nad_list_lub(Css,Phi_extra),
	ut_flat_list([Cs_star_trans,Phi_extra],Cs_comb2),
	(Max_Min=max->
	max_min_linear_expression_all(L_total,EVars,Cs_comb2,Max_Min,Maxs)
	;
	Maxs=[]
	).

generate_loop_info(Delta,Max_min,Loop,(Max_min_loop,Delta)):-
	Max_min_loop=..[Max_min,Loop].

does_not_decrease(Head,Call,L,Loop):-
	loop_ph(Head,(Loop,_),Call,Cs,_,_),
	normalize_constraint(L>=0,Positive_constraint),
	term_variables(Cs,Vars_constraint),
	nad_entails(Vars_constraint,Cs,[Positive_constraint]).


check_bad_loops(Head,Call,Exp,Max_Min,Loop,Info):-
	loop_ph(Head,(Loop,_),Call,Cs,_,_),
	normalize_constraint( D=Exp ,Constraint),
	Cs_1 = [ Constraint | Cs],
	(Max_Min=max->
	  nad_minimize(Cs_1,[D],[Delta]),
	  Pos_loop=max(Loop),
	  Neg_loop=min(Loop)
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



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
generate_constraints([],_Max_min,Dicc,[],Dicc).
generate_constraints([bound(Expression,Bounded)|More],Max_min,Dicc,[Constr|Constraints],Dicc_out):-
	foldl(insert_in_dicc,Bounded,(Dicc,[]),(Dicc1,Var_list)),
	write_sum(Var_list,Sum),
	(Max_min=max->
	normalize_constraint(Sum =< Expression,Constr)
	;
	normalize_constraint(Sum >= Expression,Constr)
	),
	generate_constraints(More,Max_min,Dicc1,Constraints,Dicc_out).
	

inverse_map((Name,Var),Dicc_inv,Dicc_inv1):-
	insert_lm(Dicc_inv,Var,Name,Dicc_inv1).

insert_in_dicc(Elem,(Dicc,Var_list),(Dicc,[Var|Var_list])):-
	lookup_lm(Dicc,Elem,Var),!.
insert_in_dicc(Elem,(Dicc,Var_list),(Dicc1,[Var|Var_list])):-
	insert_lm(Dicc,Elem,Var,Dicc1).
	
cstr_generate_top_expr_from_poly(Projected,Max_min,Dicc,Extra_vars,New_top_exps2):-
	get_linear_norms_from_constraints(Projected,Max_min,Extra_vars,Norms),
	maplist(get_top_exp_from_norm(Dicc),Norms,New_top_exps),
	limit_top_expression_selection(New_top_exps,Max_min,Dicc,New_top_exps2).
	
limit_top_expression_selection(Top_exps,Max_min,Dicc,Top_exps2):-
	sort_with(Top_exps,worse_top_exp,Sorted_top_exps),
	(Max_min=max->
		Sorted_top_exps1=Sorted_top_exps
	;
		reverse(Sorted_top_exps,Sorted_top_exps1)
	),
	(get_param(maximize_fast,[N]);N=1),
	length(Dicc,N_vars),
	repeat_n_times(N_vars,N,Counters),
	maplist(tuple,_,Vars,Dicc),
	from_list_sl(Vars,Vars_set),
	maplist(tuple,Vars_set,Counters,Counters_dicc),
	get_filtered_top_exps(Sorted_top_exps1,Counters_dicc,Top_exps2).

worse_top_exp(bound(Exp1,_),bound(Exp2,_)):-
	number(Exp1),number(Exp2),!,Exp1 > Exp2.
worse_top_exp(bound(Exp1,_),bound(Exp2,_)):-
	\+number(Exp1),number(Exp2),!.	
worse_top_exp(bound(_Exp1,Bounded),bound(_Exp2,Bounded2)):-
	length(Bounded,N1),
	length(Bounded2,N2),
	N2 > N1.
	
update_ub_counters([],_,[],[]).
update_ub_counters(Counters,[],[],Counters):-!.
update_ub_counters([(Loop,N)|Cnts],[Loop|Loops],Excluded,Counters):-!,
	N1 is N-1,
	(N1 > 0-> 
	   Counters=[(Loop,N1)|Counters_aux],
	   Excluded=Excluded1
	   ;
	   Counters=Counters_aux,
	   Excluded=[Loop|Excluded1]
	   ),
	update_ub_counters(Cnts,Loops,Excluded1,Counters_aux).
update_ub_counters([(Loop,N)|Cnts],[Loop2|Loops],Excluded,[(Loop,N)|Counters_aux]):-
	Loop @< Loop2,!,
	update_ub_counters(Cnts,[Loop2|Loops],Excluded,Counters_aux).	
	
update_ub_counters([(Loop,N)|Cnts],[Loop2|Loops],Excluded,Counters_aux):-
	Loop @> Loop2,
	update_ub_counters([(Loop,N)|Cnts],Loops,Excluded,Counters_aux).		
	
get_filtered_top_exps([],_,[]):-!.
get_filtered_top_exps(_,[],[]):-!.
get_filtered_top_exps([bound(Exp,Bounded)|Tops],Counters,[bound(Exp,Bounded)|Selected]):-
		update_ub_counters(Counters,Bounded,Excluded,Counters2),
		from_list_sl(Excluded,Excluded_set),
		filter_tops_with_excluded(Tops,Excluded_set,Tops2),
		get_filtered_top_exps(Tops2,Counters2,Selected).

filter_tops_with_excluded([],_,[]).
filter_tops_with_excluded([bound(Exp,Bounded)|Tops],Excluded,Tops1):-
	difference_sl(Bounded,Excluded,Bounded1),
	(Bounded1=[]->
	Tops1=Tops2
	;
	Tops1=[bound(Exp,Bounded1)|Tops2]
	),
	filter_tops_with_excluded(Tops,Excluded,Tops2).
		
get_top_exp_from_norm(Dicc,norm(Its,Exp),bound(Exp,Bounded)):-
	foldl(substitute_its_by_bounded(Dicc),Its,[],Bounded).	
	

substitute_its_by_bounded(Dicc,It_var,Accum,[Elem|Accum]):-
	lookup_lm(Dicc,It_var,Elem).
	
get_linear_norms_from_constraints([],_Max_min,_,[]).
get_linear_norms_from_constraints([C|Cs],max,Its_total,Norms):-
	normalize_constraint_wrt_vars(C,Its_total,C1),!,
	(C1= (Its =< Exp)->
		Norms=[norm(Its,Exp)|Norms_aux]
		;
		Norms=Norms_aux
	),
	get_linear_norms_from_constraints(Cs,max,Its_total,Norms_aux).
	
get_linear_norms_from_constraints([C|Cs],min,Its_total,Norms):-
	normalize_constraint_wrt_vars(C,Its_total,C1),!,
	(C1= (Its >= Exp)->
		Norms=[norm(Its,Exp)|Norms_aux]
		;
		Norms=Norms_aux
	),
	get_linear_norms_from_constraints(Cs,min,Its_total,Norms_aux).	
	
get_linear_norms_from_constraints([_C|Cs],Max_min,Its_total,Norms):-
	get_linear_norms_from_constraints(Cs,Max_min,Its_total,Norms).	
	

	
%! maximize_linear_expression_all(+Linear_Expr_to_Maximize:linear_expression,+Vars_of_Interest:list(var),+Context:polyhedron, -Maxs:list(linear_expression)) is det
% This predicate obtains a list of linear expressions Maxs that are an upper bound of Linear_Expr_to_Maximize
% according to Context and are only expressed in terms of Vars_of_Interest.
% The length of Maxs is limited by the input parameter -maximize_fast N.
% If no upper bound is found, the predicate returns an empty list.
max_min_linear_expression_all(Number,_,_,_, [Number]) :-
	number(Number),!.

max_min_linear_expression_all(Linear_Expr_to_Maximize, Vars_of_Interest, Context,Max_Min, Maxs_out2) :-
	(get_param(maximize_fast,[N])->
		true
		;
		N=1),
	max_min_linear_expression_all_n(N,Linear_Expr_to_Maximize, Vars_of_Interest, Context,Max_Min, Maxs_out2).


max_min_linear_expression_all_n(N,Linear_Expr_to_Maximize, Vars_of_Interest, Context,Max_Min, Maxs_out) :-
	%Create a new variable and set it to the linear expression we want to maximize
	normalize_constraint(R=Linear_Expr_to_Maximize,Exp),
	% Polyhedral projection so Cs is expressed in terms of Vars_of_Interest and R
	nad_project([R|Vars_of_Interest],[Exp|Context],Cs),
	% Extract upper bound sintactically
	extract_all_possible(Cs, R, Max_Exprs),
	get_right_sides(Max_Exprs,Max_Min,Maxs),
	from_list_sl(Maxs,Maxs_set),
	length(Maxs_set,Curr_length),
	Rest is N-Curr_length,
	% If we have not iferred enough upper bounds
	(Rest > 0 ->
	term_variables(Maxs,Used_vars),
	from_list_sl(Used_vars,Used_vars_set),
	from_list_sl(Vars_of_Interest,Vars_of_Interest_set),
	(Used_vars_set=[Elem|_]->
	%remove a variable from the variables of interest
	   difference_sl(Vars_of_Interest_set,[Elem],Vars_of_Interest1),
	%and try to obtain new expressions with a recursive call
	   max_min_linear_expression_all_n(Rest,R,Vars_of_Interest1,Cs,Max_Min,Maxs1),
	   union_sl(Maxs1,Maxs_set,Maxs_out)
	   ;
	   Maxs_out=Maxs_set
	 ),!
	 ;
	 %if we too many upper bounds, take the first N ones
	   ut_split_at_pos(Maxs_set,N,Maxs_out,_)
	 ).

%! extract_all_possible(+Cs:list(linear_constraint),+R:var,-M:list(linear_constraints)) is det
% express all the constraints in Cs that contain R as R rel_op	C0+C1*X1+...+CN*XN
% where rel_op in [=<,>=,=].
extract_all_possible([],_,[]).
extract_all_possible([C|Cs],R,Ms) :-
	( normalize_constraint_wrt_var(C,R,M) -> 
	    Ms = [M|Ms_aux] 
	    ; 
	    Ms = Ms_aux 
	),
	extract_all_possible(Cs,R,Ms_aux).
	
%! get_right_sides(+Es:list(linear_constraint),-Maxs:list(linear_expression)) is det
% collect all linear expressions Max such that _=<Max is in Es.
% If there is one constraint _=Max, we only get such linear expression.
get_right_sides(Es,_,[Max]):-
	member(_=Max,Es),!.
		
get_right_sides(Es,Max_Min,Maxs):-
	get_right_sides_1(Es,Max_Min,Maxs).
	
get_right_sides_1([],_,[]).
get_right_sides_1([_=<Max|Es],max,[Max|Maxs]):-!,
	get_right_sides_1(Es,max,Maxs).
get_right_sides_1([_>= Min|Es],min,[Min|Maxs]):-!,
	get_right_sides_1(Es,min,Maxs).	
	
get_right_sides_1([_|Es],Max_Min,Maxs):-
	get_right_sides_1(Es,Max_Min,Maxs).	