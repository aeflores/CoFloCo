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

:- module(constraints_maximization,[compress_sets_constraints/4,
				  maximize_constraints_set/4,
				  maximize_internal_elements/4,
				  maximize_loop/4,
				  compress_or_constraints/4,
				  maximize_linear_expression_all/4]).
				  
:- use_module('../IO/params',[get_param/2]).
:- use_module('../utils/cofloco_utils',[
	        zip_with_op/4,
			tuple/3,
			normalize_constraint/2,normalize_constraint_wrt_var/3,
			repeat_n_times/3,
			assign_right_vars/3]).
:- use_module('../utils/polyhedra_optimizations',[nad_entails_aux/3,
			slice_relevant_constraints_and_vars/5,
			nad_consistent_constraints_group/2]).			

:- use_module('../utils/cost_expressions',[cexpr_maximize/4,
					      is_linear_exp/1]).

:- use_module(stdlib(utils),[ut_flat_list/2,ut_split_at_pos/4]).
:- use_module(stdlib(set_list)).
:- use_module(stdlib(list_map)).
:- use_module(stdlib(multimap)).
:- use_module(stdlib(numeric_abstract_domains),[
						nad_project/3,nad_entails/3,nad_normalize/2,
						nad_consistent_constraints/1]).
										
						
%! maximize_internal_elements(+Cost:cost_structure,+Vars:list_set(var),+Cs:polyhedron,-Cost2:cost_structure) is det
% Maximize all the elements inside the top level loops
% of the cost structure Cost with respect to the variables Vars according to Cs				
maximize_internal_elements(cost(Base,Loops,Constr),Vars,Cs,cost(MaxBase,New_loops,Constr)):-
	cexpr_maximize(Base,Vars,Cs,MaxBase),
	maplist(maximize_loop(Vars,Cs),Loops,New_loops).

%! maximize_loop(+Vars:list_set(var),+Cs:polyhedron,+Loop:loop_cost,-Loop2:loop_cost) is det
% Maximize all the elements of the loop
% with respect to the variables Vars according to Cs
maximize_loop(Vars,Cs,loop(It_var,Base,Loops,Constr),loop(It_var,MaxBase,New_loops,Constr_max)):-
	cexpr_maximize(Base,Vars,Cs,MaxBase),
	maplist(maximize_loop(Vars,Cs),Loops,New_loops),
	maximize_constraints_set(Constr,Vars,Cs,Constr_max).						

%! maximize_constraints_set(+Set:set_list(norm),+Cs:polyhedron,+Vars:list_set(var),-Maximized_set:set_list(norm)) is det
% Maximize all norms in Set
% with respect to the variables Vars according to Cs
maximize_constraints_set(Set,Vars,Cs,Maximized_set):-
	annotate_norms(Vars,Cs,Set,Set_annotated),
	maximize_constrs_individually(Set_annotated,[],Maximized_set).

%! annotate_norms(+Vars:list_set(var),+Cs:polyhedron,+Norms:list_set(norm),-Annotated_norms:list_map(norm,(flag,list(cost_expression)))) is det
% Creates a map that relates each norm with a list of maximized expressions and a flag
% the flag can be 'linear' or 'no_linear' depending on the nature of the norm's expression
%
% In order to be efficient, extract the set of expressions from the norms first,
% maximize them and then relate them to their norms again.
annotate_norms(Vars,Cs,Norms,Annotated_norms):-
	maplist(zip_with_op(norm),_,Exps,Norms),
	from_list_sl(Exps,Exps_set),
	maplist(maximize_expression(Vars,Cs),Exps_set,Maximized_exps),
	maplist(tuple,Exps_set,Maximized_exps,Maximized_map),
	annotate_norms_1(Norms,Maximized_map,Annotated_norms).

%! maximize_expression(+Vars:list_set(var),+Cs:polyhedron,+Expression:cost_expression,-Flag_Maxs:(Flag,list(cost_expressions))) is det
% Maximize Expression with respect to Vars and according to Cs
% if Expression is linear, obtain a list of separate constraints
% otherwise, obtain a single expression
maximize_expression(Vars,Cs,Expression,(linear,Maxs)):-
	is_linear_exp(Expression),!,
	term_variables(Expression,Vars_constraint),
    slice_relevant_constraints_and_vars(Vars_constraint,Vars,Cs,Vars1,Cs1),
	maximize_linear_expression_all(Expression,Vars1,Cs1,Maxs).
	
maximize_expression(Vars,Phi,Expression,(no_linear,Maxs)):-
	term_variables(Expression,Vars_constraint),
	slice_relevant_constraints_and_vars(Vars_constraint,Vars,Phi,Vars1,Phi1),  
	cexpr_maximize(Expression,Vars1,Phi1,L1),
	(L1==inf->
	   Maxs=[]
	   ;
	   Maxs=[L1]
	   ).

%! annotate_norms_1(+Norms:list_set(norm),+Map:list_map(cost_expression,(flag,list(cost_expression))),-Norm_pairs:list_map(norm,(flag,list(cost_expression)))) is det
% associate each norm in Norms to  pair (flag,list(cost_expression))
% that represents the maximized expressions of the norm and return the pairs in Norm_pairs.
% If a norm has no maximization, it is eliminated.
annotate_norms_1([],_Map,[]).
annotate_norms_1([norm(Its,Exp)|Norms],Map,Norm_pairs):-
	lookup_lm(Map,Exp,Maximized_pair),
	(Maximized_pair=(_,[])->
	   Norm_pairs=Norm_pairs_aux
	   ;
	   Norm_pairs=[(norm(Its,Exp),Maximized_pair)|Norm_pairs_aux]
	   ),
	annotate_norms_1(Norms,Map,Norm_pairs_aux).

%! maximize_constrs_individually(+Norm_map:list_map(norm,(flag,list(cost_expression))),+Max_cs_accum:list_set(norm),-Max_cs:list_set(norm)) is det
% Add new norms to Max_cs_accum from the pairs of norms in Norm_map
maximize_constrs_individually([],Max_cs,Max_cs).
maximize_constrs_individually([(norm(Its,_),(_,Maxs))|More],Max_cs_accum,Max_cs):-
	maplist(zip_with_op(norm,Its),Maxs,Max_cs1),
	from_list_sl(Max_cs1,Max_cs1_set),
	union_sl(Max_cs1_set,Max_cs_accum,Max_cs_accum2),
	maximize_constrs_individually(More,Max_cs_accum2,Max_cs).
	

%! compress_sets_constraints(+Norm_sets:list(list_set(norm)),+Vars:list(var),+Cs:polyhedron,-New_constr:list_set(norm)) is det
% given a list of norm sets, maximize all the sets and try to compress
% norms that belong to different sets.
compress_sets_constraints([],_,_,[]).
compress_sets_constraints([Set1|More],Vars,Cs,New_constr):-
	maplist(annotate_norms(Vars,Cs),[Set1|More],[List1_ann|MoreList_ann]),
	compress_sets_constraints_1(MoreList_ann,List1_ann,Vars,Cs,New_constr).


%! compress_set_constraints_1(+Norm_maps:list(list_map(norm,(flag,list(cost_expression)))),+Carry:list_map(norm,(flag,list(cost_expression))),+Vars:list(var),+Cs:polyhedron,-New_constr:list_set(norm)) is det
% given a list of norm sets, annotated with their maximization Norm_maps and Carry
% try to compress the norms using Carry to accumulate the compressed norms
% or the individual norms that could not be compressed.
% In the end, substitute the pairs by their corresponding norms with
% maximize_constrs_individually/3.
compress_sets_constraints_1([],Carry,_,_,New_constr):-
	maximize_constrs_individually(Carry,[],New_constr).
compress_sets_constraints_1([Set|More],Carry,Vars,Phi,New_constr):-
	length(Carry,N),
	repeat_n_times(N,no,Compressed_Cnt),
	compress_two_sets(Set,Carry,Compressed_Cnt,Vars,Phi,[],Compr),
%Disconnecting compression
%	unions_sl([Set,Carry],Carry1),
	compress_sets_constraints_1(More,Compr,Vars,Phi,New_constr).

%! compress_two_sets(+Set1:list_map(norm,(flag,list(cost_expression))),+Set2:list_map(norm,(flag,list(cost_expression))),Compressed_cnt:list(yes_no),+Vars:list(var),+Phi:polyhedron,+Compr_accum:list_map(norm,(flag,list(cost_expression))),-Compr_out:list_map(norm,(flag,list(cost_expression)))) is det
% given two sets of annotated norms, try to compress all the norms in Set1 with all
% the elements of Set2.
%
% Compr_out contains the accumulated norms Compr_accum, the compressed norms
% and the norms from Set1 and Set2 that could not be compressed.
% The flags in Compressed_Cnt record which elements of Set2 have been compressed.
compress_two_sets([],Set2,Compressed_Cnt,_,_,Compr,Compr2):-
	exclude_compressed(Set2,Compressed_Cnt,Set2_p),
	union_sl(Set2_p,Compr,Compr2).
	
compress_two_sets([C|Set1],Set2,Compressed_Cnt,Vars,Phi,Compr_accum,Compr_out):-
	try_compress(Set2,Compressed_Cnt,C,Vars,Phi,no,Compr_accum,Compressed_Cnt2,Compr_accum2),
	compress_two_sets(Set1,Set2,Compressed_Cnt2,Vars,Phi,Compr_accum2,Compr_out).

exclude_compressed([],[],[]).
exclude_compressed([X|Xs],[no|Ns],[X|Xs_p]):-!,
	exclude_compressed(Xs,Ns,Xs_p).
exclude_compressed([_X|Xs],[_|Ns],Xs_p):-!,
	exclude_compressed(Xs,Ns,Xs_p).	
	

%! try_compress(+Set:list_map(norm,(flag,list(cost_expression))),+Compressed_Cnts:list(yes_no),+C2:(norm,(flag,list(cost_expression))),+Vars:list(var),+Phi:polyhedron,IsCompressed:flag,+Compr_accum:list_map(norm,(flag,list(cost_expression))),-Compressed_Cnts2:list(yes_no),-Compr:list_map(norm,(flag,list(cost_expression)))) is det
% try to compress C2 with all the elements of Set.
% for each element C1 in Set, try to maximize it with C2 and see if the resulting
% expressions can be smaller that maximizing each constraint independently (using can_be_smaller/4).
% Also check that the resulting expression is a sound maximization of both 
% of the constraints with bigger_than_parts/4.
%
% Update the flags yes_no of each constraint of Set and keep a flag for C2.
% at the end, add C2 to the compressed constraints if we could compress it with any other constraint
try_compress([],[],C2,_,_,IsCompressed,Compr,[],Compr2):-
	(IsCompressed=no->
	  insert_sl(Compr,C2,Compr2)
	  ;
	  Compr2=Compr
	  ).

try_compress([C1|More],[_Cnt|Compressed_Cnts],C2,Vars,Phi,_IsCompressed,Compr_accum,[yes|Compressed_Cnts2],Compr):-
	C1=(norm(Its1,L1),(linear,L1M_list)),\+term_variables(L1,[]),
	C2=(norm(Its2,L2),(linear,L2M_list)),\+term_variables(L2,[]),
	term_variables((L1,L2),Vars_constraint),
    slice_relevant_constraints_and_vars(Vars_constraint,Vars,Phi,Vars1,Phi1),	   
	maximize_linear_expression_all(L1+L2,Vars1,Phi1,L12M_list),
	
	include(can_be_smaller(L1M_list,L2M_list,Phi1),L12M_list,Compressed_expressions1),
	include(bigger_than_parts(L1,L2,Phi1),Compressed_expressions1,Compressed_expressions),	
    Compressed_expressions\=[],!,
	union_sl(Its1,Its2,Its_new),
	insert_sl(Compr_accum,(norm(Its_new,L1+L2),(linear,Compressed_expressions)),Compr_accum2),
	try_compress(More,Compressed_Cnts,C2,Vars,Phi,yes,Compr_accum2,Compressed_Cnts2,Compr).

try_compress([_C1|More],[Cnt|Compressed_Cnts],C2,Vars,Phi,IsCompressed,Compr_accum,[Cnt|Compressed_Cnts2],Compr):-
	try_compress(More,Compressed_Cnts,C2,Vars,Phi,IsCompressed,Compr_accum,Compressed_Cnts2,Compr).

%! can_be_smaller_1(+L1M_list:list(linear_expression),+L2M_list:list(linear_expression),+Cs:polyhedron,+L12M:linear_expression) is semidet
% succeeds if L12M can be smaller than all the combinations of L1M_list and L2M_list
% under the constraints of Cs
can_be_smaller([],_,_,_):-!.
can_be_smaller(_,[],_,_):-!.
can_be_smaller([L1|L1M_list],L2M_list,Cs,L12M):-
	can_be_smaller_1([L1|L1M_list],L2M_list,Cs,L12M).
	
can_be_smaller_1([],_L2M_list,Cs,_L12M):-nad_consistent_constraints(Cs).
can_be_smaller_1([L1|L1M_list],L2M_list,Cs,L12M):-
	maplist(get_smaller_constraint(L1,L12M),L2M_list,Constraints),
	append(Constraints,Cs,Cs2),
	can_be_smaller_1(L1M_list,L2M_list,Cs2,L12M).

get_smaller_constraint(L1,L12M,L2,Constraint):-	
    normalize_constraint((L1+L2)>=(L12M+1),Constraint).
  
%! bigger_than_parts(+L1:linear_constraint,+L2:linear_constraint,+Cs:polyhedron,+L12M:linear_constraint) is semidet
% succeeds if L12M is a valid upper bound of both L1 and L2
bigger_than_parts(L1,L2,Cs,L12M):-
	normalize_constraint(L12M>=L1,Constraint1),
	normalize_constraint(L12M>=L2,Constraint2),
	term_variables((Constraint1,Constraint2,Cs),Vars),
	nad_entails(Vars,Cs,[Constraint1,Constraint2]).
    
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! compress_or_constraints(+Sets:list(list_set(norm)),+Entry:term,+Call:term,-Norms:list_set(norm)) is det
% Given a list of sets of norms, merge norms that have the same expression.
%
% Extract a set of all the expressions and a multimap for each initial set of norms.
% Each multimap maps the expressions appearing in a set to the norms that contain
% that expression in the set.
% with the set of expressions and the multimaps we build the new norms with all the combinations
compress_or_constraints(Sets,Entry,Call,Norms):-
	term_variables((Entry,Call),Vars),
	exclude(empty_sl,Sets,Sets1),
	extract_expressions_map(Sets1,Multimap_norms,Expressions_set),
	generate_new_norms(Expressions_set,Vars,Multimap_norms,Norms).

%! extract_expressions_map(+Sets:list(list_set(norm)),-Multimaps_norms:list(multimap(cost_expression,norm)),-Expressions_set:list_set(cost_expression)) is det
% create a multimap(cost_expression,norm) for each set in Sets where
% each cost expression maps to the set of norms that contain such cost expression
%
% it creates also a set with all the expressions
extract_expressions_map(Sets,Multimaps_norms,Expressions_set):-
	maplist(create_multimap_norms,Sets,Multimaps_norms,Expressions_non_flat),
	ut_flat_list(Expressions_non_flat,Expressions),
	from_list_sl(Expressions,Expressions_set).
	
create_multimap_norms(Set_norms,Multimap_norms,Expressions):-
	maplist(zip_with_op(norm),_Its,Expressions,Set_norms),
	maplist(tuple,Expressions,Set_norms,Tuples),
	from_pair_list_mm(Tuples,Multimap_norms).

%! generate_new_norms(+Expressions:set_list(cost_expression),+Vars:list(var),+Multimaps:list(multimap(cost_expression,norm)),-Norms:set_list(norm)) is det
% generate a new set of norms from the set of norms multimaps.
% for each cost_expression, obtain the norms that have it in every set
% and generate all the possible combinations.
generate_new_norms([],_,_,[]).
generate_new_norms([Expr|Expressions],_Var,Multimaps,Norms):-
	get_norms_lists_with_expr(Multimaps,Expr,Multimaps2,Norms_lists),
	term_variables(Norms_lists,Vars),
	bagof(Norm,get_norm_combination(Norms_lists,Norm),New_norms),
	generate_new_norms(Expressions,Vars,Multimaps2,Norms_aux),
	union_sl(New_norms,Norms_aux,Norms).

%! get_norms_lists_with_expr(+Multimaps:list(multimap(cost_expression,norm)),Expr:cost_expression,-Multimaps2:list(multimap(cost_expression,norm)),Norm_list:list(set_list(norm))) is det
% for each mutimap that contains the key Expr, consume the corresponding values
% and accumulate them in Norm_list.
get_norms_lists_with_expr([],_,[],[]).
get_norms_lists_with_expr([Multimap|Multimaps],Expr,[Multimap2|Multimaps2],[Norms|Norms_lists]):-
	Multimap=[(Expr2,Norms)|Multimap2],
	Expr2==Expr,!,
	get_norms_lists_with_expr(Multimaps,Expr,Multimaps2,Norms_lists).
get_norms_lists_with_expr([Multimap|Multimaps],Expr,[Multimap|Multimaps2],Norms_lists):-
	get_norms_lists_with_expr(Multimaps,Expr,Multimaps2,Norms_lists).

get_norm_combination([Norm_list],Norm):-
	member(Norm,Norm_list).
get_norm_combination([Norm_list|Norms_lists],norm(Its,Exp)):-
	member(norm(Its2,Exp),Norm_list),
	get_norm_combination(Norms_lists,norm(Its1,Exp)),
	union_sl(Its1,Its2,Its).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! maximize_linear_expression_all(+Linear_Expr_to_Maximize:linear_expression,+Vars_of_Interest:list(var),+Context:polyhedron, -Maxs:list(linear_expression)) is det
% This predicate obtains a list of linear expressions Maxs that are an upper bound of Linear_Expr_to_Maximize
% according to Context and are only expressed in terms of Vars_of_Interest.
% The length of Maxs is limited by the input parameter -maximize_fast N.
% If no upper bound is found, the predicate returns an empty list.
maximize_linear_expression_all(Number,_,_, [Number]) :-
	number(Number),!.

maximize_linear_expression_all(Linear_Expr_to_Maximize, Vars_of_Interest, Context, Maxs_out2) :-
	(get_param(maximize_fast,[N])->
		true
		;
		N=1),
	maximize_linear_expression_all_n(N,Linear_Expr_to_Maximize, Vars_of_Interest, Context, Maxs_out2).


maximize_linear_expression_all_n(N,Linear_Expr_to_Maximize, Vars_of_Interest, Context, Maxs_out) :-
	%Create a new variable and set it to the linear expression we want to maximize
	normalize_constraint(R=Linear_Expr_to_Maximize,Exp),
	% Polyhedral projection so Cs is expressed in terms of Vars_of_Interest and R
	nad_project([R|Vars_of_Interest],[Exp|Context],Cs),
	% Extract upper bound sintactically
	extract_all_possible(Cs, R, Max_Exprs),
	get_right_sides(Max_Exprs,Maxs),
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
	   maximize_linear_expression_all_n(Rest,R,Vars_of_Interest1,Cs,Maxs1),
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
get_right_sides(Es,[Max]):-
	member(_=Max,Es),!.
		
get_right_sides(Es,Maxs):-
	get_right_sides_1(Es,Maxs).
	
get_right_sides_1([],[]).
get_right_sides_1([_=<Max|Es],[Max|Maxs]):-!,
	get_right_sides_1(Es,Maxs).
get_right_sides_1([_|Es],Maxs):-
	get_right_sides_1(Es,Maxs).



