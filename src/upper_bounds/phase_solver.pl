/** <module> phase_solver

This module computes the cost structure of a phase in terms of the variables 
at the beginning and the end of the phase.
The internal elements of the cost structure are directly expressed 
in terms of the initial values of the chain.

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

:- use_module(constraints_maximization,[
				max_min_internal_elements/4,
				max_min_linear_expression_all/5]).
:- use_module(cost_equation_solver,[get_equation_cost/5]).
:- use_module(constraints_generation,[
		add_phase_upper_bounds/8,
		add_phase_lower_bounds/7]).			
				      
:- use_module('../db',[phase_loop/5,
		       loop_ph/6]).
:-use_module('../refinement/invariants',[backward_invariant/4,
			      phase_transitive_closure/5,
			      relation2entry_invariant/3,get_phase_star/4,
			      	forward_invariant/4]).
:- use_module('../IO/params',[get_param/2]).

:- use_module('../utils/cofloco_utils',[
		    zip_with_op/4,
		    tuple/3,
		    normalize_constraint/2,
		    get_it_vars_in_loop/2,
		    assign_right_vars/3,
		    bagof_no_fail/3,
		    repeat_n_times/3,
		    norm_contains_vars/2]).
:- use_module('../utils/polyhedra_optimizations',[
		    nad_project_group/3,
		    slice_relevant_constraints_and_vars/5]).

:- use_module('../utils/cost_expressions',[
						  normalize_le/2,
					      cexpr_simplify_ctx_free/2,
					      is_linear_exp/1]).
:- use_module('../utils/cost_structures',[simplify_or_cost_structure/6,
										remove_it_vars_from_constr/3]).			
		      

:- use_module(stdlib(utils),[ut_flat_list/2]).
:- use_module(stdlib(set_list)).
:- use_module(stdlib(list_map),[lookup_lm/3]).
:- use_module(stdlib(numeric_abstract_domains),[nad_entails/3,
						nad_list_lub/2,
						nad_list_glb/2,
						nad_lub/6,
						nad_glb/3,
						nad_maximize/3,
						nad_minimize/3,
						nad_consistent_constraints/1]).
:- use_module(stdlib(profiling),[profiling_start_timer/1,profiling_get_info/3,
				 profiling_stop_timer/2,profiling_stop_timer_acum/2]).
:- use_module(stdlib(counters),[counter_increase/3]).

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
	copy_term(Head,Head_total),
	%get all kinds of invariants
	%backward_invariant(Head_total,(Chain,_),_,Head_patt),
	relation2entry_invariant(Head_total,([Phase|More],_),inv(Head_total,Head,Inv_cs)),
	forward_invariant(Head,([Phase|More],_),Forward_inv_hash,Forward_inv),
	%obtain a cost structure in terms of the variables at the beginning and end of the phase
%	trace,
	compute_phase_cost(Phase,Chain,Head,Call,(Forward_inv_hash,Forward_inv),inv(Head_total,Head,Inv_cs),Cost),	

	compute_phases_cost(More,Chain,Head,Call,Costs).
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%! compute_phase_cost(Phase:phase,Head:term,Call:term,Forward_inv_hash:(int,polyhedron),Cost:cost_structure) is det
% Obtain the cost of a phase given a forward invariant.
% if the phase is non-iterative, the cost is the cost of the equation, otherwise:
% * get the cost of all the equations
% * put each cost into a new loop
% * try to take loops out by inductive compression
% * try to compress constraints from different loops
compute_phase_cost(Phase,_,Head,Call,(Forward_hash,Forward_inv),_,Cost):-
	phase_cost(Phase,Head,Call,(Forward_hash,Forward_inv2),Cost),
	Forward_inv2==Forward_inv,!,
	counter_increase(compressed_phases1,1,_).
% in a non-iterative phase, we just obtain the cost of the equation
compute_phase_cost(Non_it,_,Head,Call,(Forward_hash,Forward_inv),inv(Head_total,Head,Inv_cs),Cost1):-
	number(Non_it),
	
	profiling_start_timer(equation_cost),
	get_equation_cost(Head,Call1,(Forward_hash,Forward_inv),Non_it,Cost),
	(Call1\=none->Call1=Call;true),
	profiling_stop_timer_acum(equation_cost,_),
	
	loop_ph(Head,(Non_it,_),Call1,Phi,_,_),
	Head_total=..[_|Vars],
	%this is much cheaper than applying glb (at least in this case)
	ut_flat_list([Phi,Inv_cs,Forward_inv],Cs_total),
	%solve the internal loops and express them in terms of the variables at the beginning of the chain
	max_min_internal_elements(Cost,Vars,Cs_total,Cost1),	
	Head_total=Head,
	assert(phase_cost(Non_it,Head,Call,(Forward_hash,Forward_inv),Cost1)).

compute_phase_cost(Phase,Chain,Head,Call,(Forward_hash,Forward_inv),inv(Head_total,Head,Inv_cs),Cost):-
    %get the cost of each iterative component of the phase
	maplist(compute_phase_loop_cost(Head,Call,(Forward_hash,Forward_inv)),Phase,Loops),
	
	term_variables(Head,Head_vars),
	from_list_sl(Head_vars,Head_vars_set),
	term_variables(Call,Call_vars),
	from_list_sl(Call_vars,Call_vars_set),
	
	maplist(get_internal_norm_expressions((Call_vars_set,Head_vars_set)),Loops,Norm_exprs,INorm_exprs),
	maplist(get_loop_it_var,Loops,It_vars),
	add_phase_upper_bounds(Head,Call,Phase,Chain,It_vars,[],It_constrs,Differential_norms),
	union_sl(It_constrs,Differential_norms,New_norms),
	(get_param(negative,[])->
		add_phase_lower_bounds(Head,Call,Phase,Chain,It_vars,[],New_Inorms)
	;
		New_Inorms=[]
	),
	profiling_start_timer(flatten_loops),
	inductive_compression(Head,Call,Phase,It_vars,max,(New_norms,New_Inorms),Norm_exprs,Compressed_exps),
	inductive_compression(Head,Call,Phase,It_vars,min,(New_norms,New_Inorms),INorm_exprs,ICompressed_exps),
	extract_unrolled_loops(Loops,Compressed_exps,ICompressed_exps,Loops2,Unrolled_norms,Unrolled_Inorms),
	
	
	profiling_stop_timer_acum(flatten_loops,_),
	%eliminate iteration variables with zero cost
	%simplify_or_cost_structure(Loops_out_flat,External_constrs,Cs_transitive,Removed_it_vars,Elems2,NormsList2),
	
	union_sl(New_norms,Unrolled_norms,Constrs3),	
	union_sl(New_Inorms,Unrolled_Inorms,IConstrs3),
	Head_total=..[_|Vars],
	%this is much cheaper than applying glb (at least in this case)
	ut_flat_list([Inv_cs,Forward_inv],Cs_total),
	%solve the internal loops and express them in terms of the variables at the beginning of the chain
	maplist(maximize_internal_elements(Vars,Cs_total,Head,Call),Phase,Loops2,Loops_maximized),
	ut_flat_list(Loops_maximized,Loops3),
	Cost=cost(0,Loops3,Constrs3,IConstrs3),
	Head_total=Head,
	assert(phase_cost(Phase,Head,Call,(Forward_hash,Forward_inv),Cost)).

maximize_internal_elements(Vars,Cs,Head,Call,Loop_id,Loops,Loops_maximized):-
	loop_ph(Head,(Loop_id,_),Call,Cs_loop,_,_),
	append(Cs,Cs_loop,Cs_total),
	max_min_internal_elements(cost(0,Loops,[],[]),Vars,Cs_total,cost(0,Loops_maximized,[],[])).

	
extract_unrolled_loops(Loops,Compressed_exps,Compressed_Iexps,Loops_unrolled,Unrolled_norms2,Unrolled_Inorms2):-
	maplist(tuple,Compressed_exps1,_,Compressed_exps),
	maplist(tuple,Compressed_Iexps1,_,Compressed_Iexps),
	maplist(extract_unrolled_loop_1(Compressed_exps1,Compressed_Iexps1),Loops,Loops_unrolled,Unrolled_norms,Unrolled_Inorms),
	get_norm_combinations_greedy_mul(Compressed_exps,Unrolled_norms,[],Unrolled_norms2),
	%FIXME check this
	get_norm_combinations_greedy_mul(Compressed_Iexps,Unrolled_Inorms,[],Unrolled_Inorms2).

extract_unrolled_loop_1(Compressed_exps,Compressed_Iexps,loop(It_var,Base,Loops,Norms,INorms),[Loop|Loops_unrolled],Unrolled,IUnrolled):-
	partition(norm_contains_exp(Compressed_exps),Norms,Unrolled,Remaining),
	maplist(get_it_vars_in_constr,Unrolled,It_vars_list),
	unions_sl(It_vars_list,It_vars_set),
	partition(norm_contains_exp(Compressed_Iexps),INorms,IUnrolled,IRemaining),
	maplist(get_it_vars_in_constr,IUnrolled,IIt_vars_list),
	unions_sl(IIt_vars_list,IIt_vars_set),
	(difference_sl(IIt_vars_set,It_vars_set,[])->
	clean_remaining_norms(Remaining,It_vars_set,Remaining1),
	clean_remaining_norms(IRemaining,It_vars_set,IRemaining1),
	partition(is_loop_unrolled(It_vars_set),Loops,Loops_unrolled,Loops_left),
	Loop=loop(It_var,Base,Loops_left,Remaining1,IRemaining1)
	;
	 trace).
	


clean_remaining_norms([],_It_vars_set,[]).
clean_remaining_norms([norm(Its,Rf)|Remaining],It_vars_set,Remaining1):-
	remove_it_vars_from_constr(It_vars_set,norm(Its,Rf),norm(Diff,Rf)),
	(Diff=[]->
	    clean_remaining_norms(Remaining,It_vars_set,Remaining1)
	;
	    clean_remaining_norms(Remaining,It_vars_set,Remaining_aux),
	    Remaining1=[norm(Diff,Rf)|Remaining_aux]
	). 

	
%TODO: Rewrite
get_norm_combinations_greedy_mul([],_,Accum,Accum).
get_norm_combinations_greedy_mul([(Exp,Extra_its_maxs)|Exps],Norms,Accum,Gen_norms):-
	maplist(filter_with_exp(Exp),Norms,Rem_norms,Norms_exp),
	get_norm_combinations_greedy(Norms_exp,Extra_its_maxs,New_norms_set),
	union_sl(Accum,New_norms_set,Accum2),
	get_norm_combinations_greedy_mul(Exps,Rem_norms,Accum2,Gen_norms).

filter_with_exp(Exp,Norms,Norms_without_exp,Norms_with_exp):-
	partition(norm_contains_exp([Exp]),Norms,Norms_with_exp,Norms_without_exp).
	
get_norm_combinations_greedy(Norms,Extra_its_maxs,Gen_norms_set):-
	exclude(empty_list,Norms,Norms1),
	get_norm_combinations_greedy_1(Norms1,Extra_its_maxs,Gen_norms),
	from_list_sl(Gen_norms,Gen_norms_set).

get_norm_combinations_greedy_1([],_,[]).	
get_norm_combinations_greedy_1(Norms,(Extra_its1,Extra_its2,Maxs),Gen_norms1):-
	maplist(head_tail,Norms,[norm(Its_0,Exp)|Heads],Tails),
	exclude(empty_list,Tails,Tails1),
	foldl(accum_norm,Heads,norm(Its_0,Exp),norm(Its,Exp)),
	maplist(add_to_norm(Its,[Exp|Maxs],Extra_its2),Extra_its1,Gen_norms_aux),
	get_norm_combinations_greedy_1(Tails1,(Extra_its1,Extra_its2,Maxs),Gen_norms),
	ut_flat_list(Gen_norms_aux,Gen_norms_aux2),
	append(Gen_norms_aux2,Gen_norms,Gen_norms1).

add_to_norm(Its,Exps,Exps2,Exp,Gen_norms):-
	maplist(add_to_norm_1(Its,Exp,Exps2),Exps,Gen_norms).
add_to_norm_1(Its,Exp,Exps2,Exp2,Gen_norms):-
	maplist(add_to_norm_2(Its,Exp,Exp2),Exps2,Gen_norms).	
	
add_to_norm_2(Its,Exp1,Exp2,Exp3,norm(Its,Exp1+Exp2+Exp3)).

		
	
%! compute_phase_loop_cost(+Head:term,+Call:term,+Forward_inv_hash:(int,polyhedron),+Cs_star_trans:polyhedron,+Cs_transitive:polyhedron,+Eq_id:equation_id,-It_var_Loops_out:(var,list(loop_cost)),-External_constrs2:list(norm)) is det
% given a cost equation id that belongs to a phase:
% * get the cost of the equation
compute_phase_loop_cost(Head,Call,Forward_inv_hash,Eq_id,loop(_It_var,Base,Elems,Constrs,IConstrs)):-
	profiling_start_timer(equation_cost),
	get_equation_cost(Head,Call,Forward_inv_hash,Eq_id,cost(Base,Elems,Constrs,IConstrs)),
	profiling_stop_timer_acum(equation_cost,_).

get_internal_norm_expressions(Call_vars_set,loop(_It_var,_Base,_Elems,Constrs,IConstrs),Norm_exps_set,INorm_exps_set):-
	maplist(get_norm_exp,Constrs,Norms_exps),
	include(contains_vars(Call_vars_set),Norms_exps,Norms_exps1),
	include(is_linear_exp,Norms_exps1,Linear_norms),
	from_list_sl(Linear_norms,Norm_exps_set),
	
	maplist(get_norm_exp,IConstrs,INorms_exps),
	include(contains_vars(Call_vars_set),INorms_exps,INorms_exps1),
	include(is_linear_exp,INorms_exps1,ILinear_norms),
	from_list_sl(ILinear_norms,INorm_exps_set).
	
	

%! inductive_compression(+Loop:loop_cost,+Phi:polyhedron,+Head:term,+Cs_star_trans:polyhedron,+Cs_trans:polyhedron,+Call:term,-New_loops:list(loop_cost),-Unrolled_mult_set:list_set(norm)) is det
% * get the expressions in Norms and try to compress them inductively (unroll them)
% * split the  constraints into unrolled and not_unrolled.
% * get the interation variables that have been compressed and extract the involved loops
% * remove such iteration variables from the norms that are not unrolled
inductive_compression(Head,Call,Phase,It_vars,Max_Min,New_norms,Expressions_sets,Compressed_norms_complete):-
	phase_transitive_closure(Phase,_,Head,Call,Cs_transitive),
	unions_sl(Expressions_sets,All_expressions),	
	maplist(get_expressions_map(Expressions_sets,Phase),All_expressions,Expressions_map),
	maplist(tuple,All_expressions,_,Pairs),
	maplist(tuple,Pairs,Expressions_map,Pairs1),
	%phase_loop(Phase,_,Head,Call,Phi),
	get_phase_star(Head,Call,Phase,Cs_star_trans),
	%include(try_inductive_compression(Head,Phase,Cs_star_trans,Cs_transitive,Call),Pairs1,Compressed_norms),
	include(try_inductive_compression(Head,Phase,Cs_star_trans,Cs_transitive,Call,Max_Min),Pairs1,Compressed_norms),
	maplist(tuple,Compressed_norms1,_,Compressed_norms),
	add_extra_iterations(Compressed_norms1,Phase,It_vars,New_norms,Compressed_norms_complete).
	

try_inductive_compression(Head,Phase,Cs_star_trans,Cs_trans,Call,Max_Min,((L,(Bad_loops_info_flat,Maxs)),Expressions_map)):-
	phase_loop(Phase,_,Call,Call2,Phi),
	difference_sl(Phase,Expressions_map,Bad_loops),
	copy_term((Head,Call,Phi,L),(Call,Call2,Cs2,L2)),
	copy_term((Head,Call,L),(Head,Call2,L_total)),
	

	ut_flat_list([Cs_trans,Cs2],Cs_comb),
	Head=..[_|EVars],
	%Call2=..[_|ECall3],
	%append(EVars,ECall3,Vars),

	term_variables(Cs_comb,Vars_constraint),
	%slice_relevant_constraints_and_vars(Vars_constraint,Vars,Cs_comb,Vars1,Cs_comb1),
	(Max_Min=max->
	normalize_constraint(L+L2=<L_total,Inductive_constraint)
	;
	normalize_constraint(L+L2>=L_total,Inductive_constraint)
	),
	nad_entails(Vars_constraint,Cs_comb,[Inductive_constraint]),
	maplist(does_not_decrease(Head,Call,L),Expressions_map),
	maplist(check_bad_loops(Head,Call,L,Max_Min),Bad_loops,Bad_loops_info),
	ut_flat_list(Bad_loops_info,Bad_loops_info_flat),!,
	maplist(get_loop_cs(Call,Call2),Expressions_map,Css),
	nad_list_lub(Css,Phi_extra),
	ut_flat_list([Cs_star_trans,Phi_extra],Cs_comb2),
	(Max_Min=max->
	max_min_linear_expression_all(L_total,EVars,Cs_comb2,Max_Min,Maxs)
	;
	Maxs=[]
	).

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
	Constant is 0-Delta,
	(Constant>=0->
	   (Constant\==0 ->
	   	  Info=(Pos_loop,Constant)
	 	;
	   	  Info=[]
	   )
	 ;
	 Info=(Neg_loop,Constant)
	 ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

add_extra_iterations([],_Phase,_It_vars,_Norms,[]).
add_extra_iterations([(Exp,(Extra_its_info,Maxs))|Exps],Phase,It_vars,(Norms,INorms),[(Exp,(Extra_its1,Extra_its2,Maxs))|Exps_complete]):-
	partition(max_component,Extra_its_info,Extra_its_info_max,Extra_its_info_min),
	get_extra_iterations(Extra_its_info_max,(Phase,It_vars),Norms,max,Extra_its1),
	get_extra_iterations(Extra_its_info_min,(Phase,It_vars),INorms,min,Extra_its2),!,
	add_extra_iterations(Exps,Phase,It_vars,Norms,Exps_complete).
	
add_extra_iterations([_|Exps],Phase,It_vars,Norms,Exps_complete):-
	add_extra_iterations(Exps,Phase,It_vars,Norms,Exps_complete).	
	
max_component((max(_),_)).
	
get_extra_iterations(Extra_its_info,(Phase,It_vars),Norms,Max_Min,Extra_its_list_right):-
		maplist(tuple,Phase,It_vars,Phase_vars_dicc),
		maplist(abstract_loop_id(Phase_vars_dicc),Extra_its_info,Abstract_info),
		get_involved_it_vars(Abstract_info,Involved_it_vars),
		get_bounds_on_it_vars(Norms,Involved_it_vars,Max_Min,Bounds),
		from_list_sl(Bounds,Bounds_set),
		term_variables(Bounds_set,Vars),
		(Max_Min=max->
		  findall((Vars,Extra_its),
		  combine_extra_its_and_bounds_max(Bounds_set,Abstract_info,Extra_its)
		  , Extra_its_list)
		;
		  findall((Vars,Extra_its),
		  combine_extra_its_and_bounds_min(Bounds_set,Abstract_info,Extra_its)
		  ,Extra_its_list)
		),
		assign_right_vars(Extra_its_list,Vars,Extra_its_list_right).

abstract_loop_id(Phase_vars_dicc,(max(Loop),Cnt),(It_var,Cnt)):-
	lookup_lm(Phase_vars_dicc,Loop,It_var).
abstract_loop_id(Phase_vars_dicc,(min(Loop),Cnt),(It_var,Cnt)):-
	lookup_lm(Phase_vars_dicc,Loop,It_var).	
	
get_involved_it_vars(Abstract_info,It_vars_set):-
	maplist(tuple,It_vars,_,Abstract_info),
	from_list_sl(It_vars,It_vars_set).

get_bounds_on_it_vars([],_,_,[]).
get_bounds_on_it_vars([norm(Its,Exp)|Norms],Its1,max,Bounds):-
	intersection_sl(Its,Its1,Its2),
	(Its2\=[]->
		Bounds=[(Its2,Exp)|Bounds1]
	;
		Bounds=Bounds1
	),
	get_bounds_on_it_vars(Norms,Its1,max,Bounds1).
	
get_bounds_on_it_vars([norm(Its,Exp)|Norms],Its1,min,Bounds):-
	intersection_sl(Its,Its1,Its2),
	difference_sl(Its,Its1,Its3),
	((Its2\=[],Its3=[])->%here we are strict, we cannot eliminate iteration variables from a lower bound
		Bounds=[(Its2,Exp)|Bounds1]
	;
		Bounds=Bounds1
	),
	get_bounds_on_it_vars(Norms,Its1,min,Bounds1).
	
combine_extra_its_and_bounds_max(_Bounds_set,[],0):-!.
combine_extra_its_and_bounds_max([],_,_):-fail.
combine_extra_its_and_bounds_max([(Its,Bound)|Bounds_set],Abstract_info,Factor*Bound+Extra_its):-
	partition(info_contains_its(Its),Abstract_info,Selected,Remaining_info),
	maplist(tuple,_,Factors,Selected),
	max_list(Factors,Factor),
	foldl(filter_remaining_bound(Its),Bounds_set,[],Bounds_set1),
	combine_extra_its_and_bounds_max(Bounds_set1,Remaining_info,Extra_its).
combine_extra_its_and_bounds_max([_|Bounds_set],Abstract_info,Extra_its):-
	combine_extra_its_and_bounds_max(Bounds_set,Abstract_info,Extra_its).	

combine_extra_its_and_bounds_min(_Bounds_set,[],0):-!.
combine_extra_its_and_bounds_min([],_,0).
combine_extra_its_and_bounds_min([(Its,Bound)|Bounds_set],Abstract_info,Factor*Bound+Extra_its):-
	partition(info_contains_its(Its),Abstract_info,Selected,Remaining_info),
	maplist(tuple,_,Factors,Selected),
	length(Its,N),length(Selected,N),%we force that all iteration variables are present
	min_list(Factors,Factor),
	combine_extra_its_and_bounds_min(Bounds_set,Remaining_info,Extra_its).
combine_extra_its_and_bounds_min([_|Bounds_set],Abstract_info,Extra_its):-
	combine_extra_its_and_bounds_min(Bounds_set,Abstract_info,Extra_its).	
	
info_contains_its(Its,(It_var,_)):-
	contains_sl(Its,It_var).
	
filter_remaining_bound(Its,(Its1,Bound),Bounds_aux,Bounds_set1):-
	difference_sl(Its1,Its,Its2),
	(Its2\=[]->
	  Bounds_set1=[(Its2,Bound)|Bounds_aux]
	;
	  Bounds_set1=Bounds_aux
	).
	
%Auxiliary predicates
empty_list([]).
head_tail([H|T],H,T).
accum_norm(norm(Its_1,Exp),norm(Its_0,Exp),norm(Its,Exp)):-
	union_sl(Its_0,Its_1,Its).	

is_loop_unrolled(It_vars_set,loop(It_var,_Base,_Internal,_Norms,_INorms)):-
	contains_sl(It_vars_set,It_var).	
	
get_it_vars_in_constr(norm(Its,_L),Its_set):-
	from_list_sl(Its,Its_set).	
	
get_norm_exp(norm(_,Exp),Exp).
norm_contains_exp(Exps,norm(_,Exp)):-
	contains_sl(Exps,Exp).	
	
contains_vars((Var_set1,Var_set2),Exp):-
	term_variables(Exp,Vs),
	from_list_sl(Vs,Vs_set),
	\+intersection_sl(Var_set1,Vs_set,[]),
	\+intersection_sl(Var_set2,Vs_set,[]).

get_loop_it_var(loop(It_var,_Base,_Elems,_Constrs,_IConstrs),It_var).

get_expressions_map(Ex_sets,Phase,Exp,Map_set):-
	maplist(loop_contains_exp(Exp),Ex_sets,Phase,Map),
	ut_flat_list(Map,Map_flat),
	from_list_sl(Map_flat,Map_set).
	
get_loop_cs(Head,Call,Loop,Cs):-
	loop_ph(Head,(Loop,_),Call,Cs,_,_).
	
loop_contains_exp(Exp,Set,Loop,[Loop]):-
		contains_sl(Set,Exp),!.
loop_contains_exp(_Exp,_Set,_Loop,[]).	

