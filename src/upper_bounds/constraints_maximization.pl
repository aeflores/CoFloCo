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
				  maximize_top_expressions_in_cost_equation/6,
				  maximize_top_expressions_in_chain/6,
				  maximize_top_expressions_in_phase/5,
				  max_min_linear_expression_all/5]).
				  
:- use_module('../IO/params',[get_param/2]).
:- use_module('../db',[loop_ph/6,phase_loop/5]).
:- use_module('../utils/cofloco_utils',[
	        zip_with_op/4,
			tuple/3,
			normalize_constraint/2,
			normalize_constraint_wrt_var/3,	
			normalize_constraint_wrt_vars/3,	    
			repeat_n_times/3,
			write_sum/2,
			assign_right_vars/3]).
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
:- use_module('../utils/cost_structures',[remove_cycles_in_cost/2,name_aux_var/1]).			
:- use_module(constraints_generation,[add_phase_upper_bounds_temporary/6]).			
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
										
maximize_top_expressions_in_cost_equation(Top_exps,_Base_calls,Phi,TVars,New_top_exps,[]):-
	generate_constraints(Top_exps,[],Constraints,Dicc),
	maplist(tuple,_Names,Extra_vars,Dicc),
	from_list_sl(Extra_vars,Extra_vars_set),
	foldl(inverse_map,Dicc,[],Dicc_inv),
	append(Constraints,Phi,Phi1),
	append(Extra_vars,TVars,Total_vars),
	nad_project(Total_vars,Phi1,Projected),
	generate_top_expr_from_poly(Projected,Dicc_inv,Extra_vars_set,New_top_exps).
	
maximize_top_expressions_in_chain(Top_exps,_,Phi,Head,New_top_exps,[]):-	
	term_variables(Head,TVars),
	generate_constraints(Top_exps,[],Constraints,Dicc),
	maplist(tuple,_Names,Extra_vars,Dicc),
	from_list_sl(Extra_vars,Extra_vars_set),
	foldl(inverse_map,Dicc,[],Dicc_inv),
	append(Constraints,Phi,Phi1),
	append(Extra_vars,TVars,Total_vars),
	nad_project(Total_vars,Phi1,Projected),
	generate_top_expr_from_poly(Projected,Dicc_inv,Extra_vars_set,New_top_exps).
	
		
generate_constraints([],Dicc,[],Dicc).
generate_constraints([ub(Expression,Bounded)|More],Dicc,[Constr|Constraints],Dicc_out):-
	foldl(insert_in_dicc,Bounded,(Dicc,[]),(Dicc1,Var_list)),
	write_sum(Var_list,Sum),
	normalize_constraint(Sum=<Expression,Constr),
	generate_constraints(More,Dicc1,Constraints,Dicc_out).
	

inverse_map((Name,Var),Dicc_inv,Dicc_inv1):-
	insert_lm(Dicc_inv,Var,Name,Dicc_inv1).

insert_in_dicc(Elem,(Dicc,Var_list),(Dicc,[Var|Var_list])):-
	lookup_lm(Dicc,Elem,Var),!.
insert_in_dicc(Elem,(Dicc,Var_list),(Dicc1,[Var|Var_list])):-
	insert_lm(Dicc,Elem,Var,Dicc1).
	
generate_top_expr_from_poly(Projected,Dicc,Extra_vars,New_top_exps):-
	get_linear_norms_from_constraints(Projected,Extra_vars,Norms),
	maplist(get_top_exp_from_norm(Dicc),Norms,New_top_exps).

get_top_exp_from_norm(Dicc,norm(Its,Exp),ub(Exp,Bounded)):-
	foldl(substitute_its_by_bounded(Dicc),Its,[],Bounded).	
	
gen_top_exp_from_concrete_norm(norm(Its,Exp),ub(Exp,Its_names)):-
		maplist(its_name,Its,Its_names).

its_name(Id,[it(Id)]).
gen_top_exp_from_aux((Le,Named_var),ub(Le,Named_var)):-
	name_aux_var(Named_var).
	

		
	
is_linear_norm(norm(_Its,Exp)):-
	is_linear_exp(Exp).
	

	
maximize_top_expressions_in_phase(Costs,Head,Call,Phase,Cost_final):-
	add_phase_upper_bounds_temporary(Head,Call,Phase,_,Top_exps_new,Aux_exps_new),
	maplist(remove_cycles_in_cost,Costs,Costs_simple),
	maplist(propagate_summatory,Phase,Costs_simple,Costs_propagated,Summatories),
	maplist(maximize_top_expressions_in_loop(Head,Call,Phase),Phase,Costs_propagated,Costs_maximized),
	compute_summatories(Head,Call,Phase,Summatories,Top_exps2,Aux_exps2),
	foldl(join_cost,Costs_maximized,cost([],[],[],0),cost(Top_exps,Aux_exps,Bases,Base)),
	ut_flat_list([Top_exps_new,Top_exps2,Top_exps],Top_exps_final),
	ut_flat_list([Aux_exps_new,Aux_exps2,Aux_exps],Aux_exps_final),
	remove_cycles_in_cost(cost(Top_exps_final,Aux_exps_final,Bases,Base),Cost_final).
	
join_cost(cost(T,A,Bs,B),cost(T2,A2,B2s,B2),cost(T3,A3,B3s,B3)):-
	append(T,T2,T3),
	append(A,A2,A3),
	append(Bs,B2s,B3s),
	B3=B+B2.

propagate_summatory(Loop,cost(Top,Aux,Bases,Base),cost(Top2,Aux2,[([it(Loop)],Base)|Bases1],0),Summatories):-
	generate_initial_sum_map(Bases,[],Sum_map_initial,Bases1),
	propagate_sum_aux_backwards(Aux,Sum_map_initial,Aux2,Sum_map,Max_map),
	get_maxs(Top,Max_map,Top2),
	get_summatories(Top,Sum_map,Summatories).
	
get_maxs([],_,[]).
get_maxs([ub(Exp,Bounded)|Tops],Max_set,Tops2):-
	include(contains_sl(Max_set),Bounded,Non_summatories),
	(Non_summatories\=[]->
		Tops2=[ub(Exp,Non_summatories)|Tops1]
		;
		Tops2=Tops1
		),
	get_maxs(Tops,Max_set,Tops1).
	
get_summatories([],_,[]).
get_summatories([ub(Exp,Bounded)|Tops],Sum_map,Tops2):-
	get_mapped(Bounded,Sum_map,New_names),
	(New_names\=[]->
		Tops2=[ub(Exp,New_names)|Tops1]
		;
		Tops2=Tops1
		),
	get_summatories(Tops,Sum_map,Tops1).

generate_initial_sum_map([],Map,Map,[]).
generate_initial_sum_map([(Name,Val)|Bases],Map,Map_out,[(Name2,Val)|Bases1]):-
	lookup_lm(Map,Name,Name2),!,
	generate_initial_sum_map(Bases,Map,Map_out,Bases1).
generate_initial_sum_map([(Name,Val)|Bases],Map,Map_out,[(Name2,Val)|Bases1]):-
	name_aux_var(Name2),
	insert_lm(Map,Name,Name2,Map1),
	generate_initial_sum_map(Bases,Map1,Map_out,Bases1).
	
	
propagate_sum_aux_backwards([],Sum_map,[],Sum_map,[]).
propagate_sum_aux_backwards([ub(Index,Expr,Bounded)|Aux_ini],Sum_map_initial,Aux3,Sum_map2,Max_map3):-	
	propagate_sum_aux_backwards(Aux_ini,Sum_map_initial,Aux,Sum_map,Max_map),
	get_mapped(Bounded,Sum_map,New_names),
	include(contains_sl(Max_map),Bounded,Non_summatories),
	(Non_summatories\=[]->
		Aux2=[ub(Index,Expr,Non_summatories)|Aux],
		foldl(add_indexes_to_set,Index,Max_map,Max_map2)
	;
	  Aux2=Aux,
	  Max_map2=Max_map
	),
	(New_names\=[]->

	%this means some are multiplied (the new names can be the same as the old if they did not coicide
	update_max_set(Index,Expr,Index_max,Max_map2,Max_map3),
	update_sum_map(Index,Expr,Index_sum,Max_map3,Sum_map,Sum_map2),
	append(Index_max,Index_sum,Index_final),
	Aux3=[ub(Index_final,Expr,New_names)|Aux2]
	;
	Aux3=Aux2,
	Sum_map2=Sum_map,
	Max_map3=Max_map2
	).

get_mapped([],_,[]).
get_mapped([X|Xs],Map,[New_name|New_names]):-
	lookup_lm(Map,X,New_name),!,
	get_mapped(Xs,Map,New_names).
get_mapped([_|Xs],Map,New_names):-
	get_mapped(Xs,Map,New_names).
	
add_indexes_to_set((Name,_Var),Max_map,Max_map2):-
	insert_sl(Max_map,Name,Max_map2).
	
update_max_set(Index,Expr,Index_max,Max_set,Max_set2):-
	get_all_but_first_factor(Expr,Vars_set),
	include(pair_contains(Vars_set),Index,Index_max),
	maplist(tuple,Names,_,Index_max),
	from_list_sl(Names,Names_set),
	union_sl(Names_set,Max_set,Max_set2).
	
pair_contains(Set,(_,Var)):-
	contains_sl(Set,Var).
get_all_but_first_factor(add(Summands),Vars):-
	maplist(get_all_but_first_factor_1,Summands,Vars_list),
	unions_sl(Vars_list,Vars).
get_all_but_first_factor_1(mult([_|Rest_factors]),Vars_set):-
	term_variables(Rest_factors,Vars),
	from_list_sl(Vars,Vars_set).
	
get_first_factor(add(Summands),Vars):-	
	maplist(get_first_factor_1,Summands,Vars_list),
	unions_sl(Vars_list,Vars).
get_first_factor_1(mult([First|_]),Vars_set):-
	term_variables(First,Vars),
	from_list_sl(Vars,Vars_set).

update_sum_map(Index,Expr,Index_sum_substituted,Max_map,Sum_map,Sum_map2):-
	get_first_factor(Expr,Vars_set),
	include(pair_contains(Vars_set),Index,Index_sum),
	substitute_by_new_name(Index_sum,Max_map,Sum_map,Index_sum_substituted,Sum_map2).

substitute_by_new_name([],_Max_map,Sum_map,[],Sum_map).
substitute_by_new_name([(Name,Var)|Index_sum],Max_map,Sum_map,[(New_name,Var)|Index_sum_substituted],Sum_map3):-
%	contains_sl(Max_map,Name),!,
	(lookup_lm(Sum_map,Name,New_name),Sum_map2=Sum_map
	;
	name_aux_var(New_name),
	insert_lm(Sum_map,Name,New_name,Sum_map2)),
	substitute_by_new_name(Index_sum,Max_map,Sum_map2,Index_sum_substituted,Sum_map3).
	
	
compute_summatories(Head,Call,Phase,Summatories,Top_exps2,Aux_exps2):-
	compute_sums(Head,Call,Phase,Summatories,Top,Aux,Summatories_left),
	maplist(simple_multiplication_list(Head,Call,Phase),Phase,Summatories_left,Tops,Auxs),
	ut_flat_list([Top,Tops],Top_exps2),
	ut_flat_list([Aux,Auxs],Aux_exps2).


simple_multiplication_list(Head,Call,Phase,Loop,Sums,Tops,Auxs):-
	maplist(simple_multiplication(Head,Call,Phase,Loop),Sums,Tops,Auxs).
	
simple_multiplication(Head,Call,Phase,Loop,ub(Exp,Bounded),Top_exps_new,Aux_exps_total):-
	name_aux_var(Aux_name),
	maximize_top_expression_in_loop(Head,Call,Phase,Loop,ub(Exp,[Aux_name]),Top_exps_new,Aux_exps_new),
    Aux_exp=ub([(Aux_name,Aux_var),([it(Loop)],It_var)],add([mult([It_var,Aux_var])]),Bounded),
    append(Aux_exps_new,[Aux_exp],Aux_exps_total).
	
maximize_top_expressions_in_loop(Head,Call,Phase,Loop,cost(Top_exps,Aux,Bs,B),cost(Top_exps_new2,Aux2,Bs,B)):-
	maplist(maximize_top_expression_in_loop(Head,Call,Phase,Loop),Top_exps,Top_exps_new,Aux_exps_new),
	ut_flat_list(Top_exps_new,Top_exps_new2),
	ut_flat_list([Aux_exps_new|Aux],Aux2).

maximize_top_expression_in_loop(Head,Call,Phase,Loop,ub(Exp,Bounded),Top_exps_new,Aux_exps_new):-
	traditional_phase_maximization(Head,Call,Phase,Loop,Exp,Bounded,Top_exps_new,Aux_exps_new).
	


	
substitute_its_by_bounded(Dicc,It_var,Accum,[Elem|Accum]):-
	lookup_lm(Dicc,It_var,Elem).
	
get_linear_norms_from_constraints([],_,[]).
get_linear_norms_from_constraints([C|Cs],Its_total,Norms):-
	normalize_constraint_wrt_vars(C,Its_total,C1),!,
	(C1= (Its =< Exp)->
		Norms=[norm(Its,Exp)|Norms_aux]
		;
		Norms=Norms_aux
	),
	get_linear_norms_from_constraints(Cs,Its_total,Norms_aux).
	
get_linear_norms_from_constraints([_C|Cs],Its_total,Norms):-
	get_linear_norms_from_constraints(Cs,Its_total,Norms).	
	

extract_linear_expressions([],Aux_exps,[],Aux_exps).
extract_linear_expressions([norm(Its,Exp)|Non_linear_norms],Aux_exps_map,[ub(Elems,Exp2,Its_names)|Non_linear_norms1],Aux_exps_map_out):-
	cexpr_substitute_lin_exp_by_vars(Exp,Aux_exps_map,Exp1,Aux_exps_map1),
	term_variables(Exp1,Aux_vars),
	copy_term((Aux_vars,Exp1),(Aux_vars2,Exp2)),
	maplist(tuple,Aux_vars,Aux_vars2,Elems),
	maplist(its_name,Its,Its_names),
	extract_linear_expressions(Non_linear_norms,Aux_exps_map1,Non_linear_norms1,Aux_exps_map_out).
	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

traditional_phase_maximization(Head,Call,Phase,Loop,Exp,Bounded,Top_exps_new,[]):-
	get_phase_star(Head_total,Head,Phase,Cs_star_trans),
	loop_ph(Head,(Loop,_),Call,Cs,_,_),
	ut_flat_list([Cs_star_trans,Cs],Context),
	term_variables(Head_total,Vars_of_Interest),
	max_min_linear_expression_all(Exp, Vars_of_Interest, Context,max, Maxs_out),
	Head_total=Head,
	maplist(gen_new_exp(Bounded),Maxs_out,Top_exps_new).
	
gen_new_exp(Name,Max,ub(Max,Name)).


%TODO
compute_sums(Head,Call,Phase,Summatories,Top,Aux,Summatories_left):-
	phase_transitive_closure(Phase,_,Head,Call,Cs_transitive),
	get_phase_star(Head,Call,Phase,Cs_star_trans),
	maplist(get_top_lin_expr,Summatories,Expressions_sets),
	unions_sl(Expressions_sets,All_expressions),	
	maplist(get_expressions_map(Expressions_sets,Phase),All_expressions,Expressions_map),
	maplist(tuple,All_expressions,_,Pairs),
	maplist(tuple,Pairs,Expressions_map,Pairs1),
	include(try_inductive_compression(Head,Phase,Cs_star_trans,Cs_transitive,Call,max),Pairs1,Compressed_norms),
	maplist(tuple,Compressed_norms1,_,Compressed_norms),
	generate_top_and_aux_from_compressed(Compressed_norms1,Summatories,Top,Aux,Summatories_left).
	

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

remove_one_instance_1([ub(Exp,Bounded)|More],Exp1,Bounded,More):-
	Exp==Exp1,!.
remove_one_instance_1([Summ|More],Exp1,Bounded2,[Summ|More1]):-
			remove_one_instance_1(More,Exp1,Bounded2,More1).
			

generate_top_and_aux(Info,Maxs,Bounded,Tops,Aux):-
	exclude(is_min,Info,Info2),
	(Info2=[]->
	maplist(generate_top_exp(Bounded),Maxs,Tops),
	Aux=[]
	;
	maplist(get_factors_from_loop_info,Info2,Factors,Index),
	name_aux_var(Name_aux),
	Aux=[ub([(Name_aux,Var_aux)|Index],add([mult([Var_aux])|Factors]),Bounded)],
	maplist(generate_top_exp([Name_aux]),Maxs,Tops)
	).
	
get_factors_from_loop_info((max(Loop),1),mult([Var_aux]),([it(Loop)],Var_aux)):-!.
get_factors_from_loop_info((max(Loop),N),mult([Var_aux,N]),([it(Loop)],Var_aux)).

generate_top_exp(Bounded,Max,ub(Max,Bounded)).


is_min(	(min(_),_)).
		
get_top_lin_expr(Tops,Exps_set):-
 	maplist(get_expression_from_top,Tops,Exps),
 	from_list_sl(Exps,Exps_set).
get_expression_from_top(ub(Exp,_),Exp).
	
get_expressions_map(Ex_sets,Phase,Exp,Map_set):-
	maplist(loop_contains_exp(Exp),Ex_sets,Phase,Map),
	ut_flat_list(Map,Map_flat),
	from_list_sl(Map_flat,Map_set).
	
loop_contains_exp(Exp,Set,Loop,[Loop]):-
		contains_sl(Set,Exp),!.
loop_contains_exp(_Exp,_Set,_Loop,[]).		
	
get_loop_cs(Head,Call,Loop,Cs):-
	loop_ph(Head,(Loop,_),Call,Cs,_,_).
	
is_a_difference(Exp,Head,Call,Exp_formated):-
	copy_term((Head,Call,Exp),(Head2,Head2,Exp2)),
	normalize_le(Exp2,Constant),
	number(Constant),
	Exp_formated=Exp.
	
compress_sum(_Head,_Call,_Phase,_Loop,_Exp_formated,_Bounded,_Top_exps_new,_Aux_exps_new):-fail.

	
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
	maplist(check_bad_loops(Head,Call,L,Max_Min),Bad_loops,Bad_loops_info),
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