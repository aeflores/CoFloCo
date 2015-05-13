/** <module> phase_solver

This module computes the cost structure of a phase in terms of the variables 
at the beginning and the end of the phase.
The internal elements of the cost structure are directly expressed 
in terms of the initial values of the chain.


Specific "data types" of this module:
  * rf_structure:list(int-val(list(equation_id),linear_expression,list((equation_id,int)),list(equation_id),cost_expression))
    This data structure is a sorted list
    of ranking functions that are sorted by the number of dependencies they have.
    each element contains the specific dependencies in two categories: the Increment_deps
    and the Unknown_deps. The equations in Increment_deps increment the ranking function by a
    constant, the Unkown_deps reset the value of the ranking function.
    Finally, the last part of the ranking function contains the additional expression
    that has to be added to the rf to account for dependencies that have been already removed
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

:- use_module(constraints_maximization,[compress_or_constraints/5,
				max_min_internal_elements/4,
				max_min_linear_expression_all/5]).
:- use_module(cost_equation_solver,[get_equation_cost/5]).
			      
:- use_module('../db',[phase_loop/5,
		       loop_ph/6]).
:-use_module('../refinement/invariants',[backward_invariant/4,
			      phase_transitive_closure/5,
			      relation2entry_invariant/3,get_phase_star/4,
			      	forward_invariant/4]).
:- use_module('../ranking_functions',[
				      ranking_function/4,
				      partial_ranking_function/7]).
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
:- use_module('../utils/cost_structures',[simplify_or_cost_structure/6]).					      

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

%rf_limit(-N:int) is det
% stablish the maximum number of ranking functions for the whole phase that are to be considered
rf_limit(N):-
	get_param(n_rankings,[N]).


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
	add_rfs(Head,Call,Phase,Chain,It_vars,[],It_constrs,Differential_norms),
	union_sl(It_constrs,Differential_norms,New_norms),
	(get_param(negative,[])->
		add_inverse_rfs(Head,Call,Phase,Chain,It_vars,[],New_Inorms)
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
%! remove_it_vars_from_constr(+It_vars_set:list_set(var),+Norm:norm,-Filtered_constr:norm) is det
%  remove the Iteration variables in It_vars_set from the norm Norm
remove_it_vars_from_constr(It_vars_set,norm(Its,Rf),norm(Difference,Rf)):-
	from_list_sl(Its,Its_set),
	difference_sl(Its_set,It_vars_set,Difference).	
	
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
get_norm_combinations_greedy_1(Norms,(Extra_its,Maxs),Gen_norms1):-
	maplist(head_tail,Norms,[norm(Its_0,Exp)|Heads],Tails),
	exclude(empty_list,Tails,Tails1),
	foldl(accum_norm,Heads,norm(Its_0,Exp),norm(Its,Exp)),
	maplist(add_to_norm(Its,[Exp|Maxs]),Extra_its,Gen_norms_aux),
	get_norm_combinations_greedy_1(Tails1,Extra_its,Gen_norms),
	ut_flat_list(Gen_norms_aux,Gen_norms_aux2),
	append(Gen_norms_aux2,Gen_norms,Gen_norms1).

add_to_norm(Its,Exps,Exp2,Gen_norms):-
	maplist(add_to_norm_1(Its,Exp2),Exps,Gen_norms).
add_to_norm_1(Its,Exp1,Exp2,norm(Its,Exp1+Exp2)).

		
	
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
add_extra_iterations([(Exp,(Extra_its_info,Maxs))|Exps],Phase,It_vars,(Norms,INorms),[(Exp,(Extra_its,Maxs))|Exps_complete]):-
	partition(max_component,Extra_its_info,Extra_its_info_max,Extra_its_info_min),
	get_extra_iterations(Extra_its_info_max,(Phase,It_vars),Norms,max,Extra_its1),
	get_extra_iterations(Extra_its_info_min,(Phase,It_vars),INorms,min,Extra_its2),!,
	append(Extra_its1,Extra_its2,Extra_its),
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

abstract_loop_id(Phase_vars_dicc,(Loop,Cnt),(It_var,Cnt)):-
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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! add_rfs(Head:term,Call:term,Phase:phase,Chain:chain,It_vars:list(var),Removed_vars:list_set(var),Abstract_norms2:list(norm),Differential_norms:list(norm)) is det
% given a Phase in a Chain generate 2 sets of norms that bound the number of iterations
% of each component of the Phase. 
%  * Abstract_norms2 depend on the initial variables of the phase (the ones of Head)
%  * Differential_norms depend on both the initial and the final variables of the phase (Head and Call)
%
% the iteration variables in Removed vars are excluded form the generated norms.
% It_vars contains the concrete variables that correspond to each of the loops of Phase.
add_rfs(Head,Call,Phase,Chain,It_vars,Removed_vars,Abstract_norms2,Differential_norms):-
	maplist(tuple,Phase,It_vars,It_var_dictionary),
	%rf_limit establishes how many bounds we want to generate per loop
	rf_limit(Max),
	length(Phase,N_loops),
	repeat_n_times(N_loops,Max,Counters),
	maplist(tuple,Phase,Counters,Phase_counters),
	% collect all the ranking functions and their dependencies
	% sort them according to the number of dependencies
	obtain_initial_rf_stucture(Head,Chain,Phase,Structure),
    % incrementally find upper bounds for each of the phases until the counters reach 0,
    % the available ranking functions are all consumed or
    % we find a ranking function with unresolved dependencies
	find_phase_upper_bounds(Structure,Phase_counters,(Head,Phase,Chain),[],Concrete_norms),
	%substitute the cost_equation_id of the phase by the corresponding iteration variables
	maplist(abstract_norms(It_var_dictionary),Concrete_norms,Abstract_norms),
	% remove the iteration variables of Removed_vars
	maplist(remove_it_vars_from_constr(Removed_vars),Abstract_norms,Abstract_norms1),
	exclude(empty_norm,Abstract_norms1,Abstract_norms2),
	%generate new norms by taking the difference between the norm in terms of Head 
	% and the norm in terms of Call
	get_differential_norms(Abstract_norms2,Head,Call,Differential_norms).

%FIXME: basic treatment
add_inverse_rfs(Head,Call,Phase,_Chain,It_vars,[],INorms):-!,
	from_list_sl(It_vars,It_vars_set),
	(find_lower_bound(Head,Call,Phase,LB)->
	    INorms=[norm(It_vars_set,LB)]
	;
	    INorms=[]    
	),!.

add_inverse_rfs(_Head,_Call,_Phase,_Chain,_It_vars,_Removed_it_vars,[]).

find_lower_bound(Head,Call,Phase,LB):-
	ranking_function(Head,_Chain,Phase,Rf),
	copy_term((Head,Rf),(Call,Rf1)),
	phase_loop(Phase,_,Head,Call,Phi),
	normalize_constraint( D=Rf-Rf1 ,Constraint),
	Cs_1 = [ Constraint | Phi],
	nad_maximize(Cs_1,[D],[Delta1]),
	normalize_le(1/Delta1*(Rf-Rf1),LB).
	
%! abstract_norms(+Dictionary:list_map(equation_id,var),+Norm_concrete:norm,-Norm_abstract:norm) is det
% substitute the "iteration variables" of Norm_concrete that are equation_ids
% by the corresponding real iteration variables
abstract_norms(Dictionary,norm(Its,Exp),norm(Its3,Exp)):-
	maplist(lookup_lm(Dictionary),Its,Its2),
	from_list_sl(Its2,Its3).

empty_norm(norm([],_)).
	
%! 	get_differential_norms(+Norms:list(norm),+Head:term,+Call:term,-Norms_out:list(norm)) is det
% for every norm that is a linear expression, we create a new norm that
% is the difference between the initial value and the final value of the norm.
% That is, the norm expressed in terms of Head and Call.
get_differential_norms([],_Head,_Call,[]).
get_differential_norms([norm(Its,Exp)|Norms],Head,Call,[norm(Its,Exp_diff)|Norms_out]):-
	is_linear_exp(Exp),!,
	copy_term((Head,Exp),(Call,Exp_2)),
	cexpr_simplify_ctx_free(Exp-Exp_2,Exp_diff),
	get_differential_norms(Norms,Head,Call,Norms_out).
	
get_differential_norms([norm(_Its,_Exp)|Norms],Head,Call,Norms_out):-
	get_differential_norms(Norms,Head,Call,Norms_out).	
	

%! obtain_initial_rf_stucture(Head:term,Chain:chain,Phase:phase,Structure:rf_structure) is det
% get all the ranking functions of the phase Phase in the chain Chain.
% create a data structure Structure.
%
% rf_structure:list(int-val(list(equation_id),linear_expression,list((equation_id,int)),list(equation_id),cost_expression))
% This data structure is a sorted list
% of ranking functions that are sorted by the number of dependencies they have.
% each element contains the specific dependencies in two categories: the Increment_deps
% and the Unknown_deps. The equations in Increment_deps increment the ranking function by a
%constant, the Unkown_deps reset the value of the ranking function.
% Finally, the last part of the ranking function contains the additional expression
% that has to be added to the rf to account for dependencies that have been already removed
obtain_initial_rf_stucture(Head,Chain,Phase,Structure):-
	bagof_no_fail(0-val(Phase,Rf,[],[],0),
	ranking_function(Head,Chain,Phase,Rf)
	   ,Rfs),
	bagof_no_fail(NDeps-val(Loops,Rf,Increment_deps,Unknown_deps_simple,0),
	Deps^Deps_type^Map_dependencies^Unknown_deps^Ignored^
	(
			partial_ranking_function(Head,Chain,Phase,Loops,Rf,Deps,Deps_type),
			maplist(tuple,Deps,Deps_type,Map_dependencies),			
			length(Map_dependencies,NDeps),
			partition(increment_dep,Map_dependencies,Increment_deps,Unknown_deps),
			maplist(tuple,Unknown_deps_simple,Ignored,Unknown_deps)
		
			),Deps_structure),
	%order ranking function by number of dependencies
	keysort(Deps_structure,Sorted_structure),
	append(Rfs,Sorted_structure,Structure).

increment_dep((_,N)):-number(N).	
	
%! find_phase_upper_bounds(+Structure:rf_structure,+Counters:list_map(equation_id,int),+Phase_info:(term,phase,chain),+Norms_accum:list(norm),-Concrete_norms:list(norm))	is det
% visit the rf_structure until all the needed norms have been obtained (Counters=[]);
% the structure is empty (Structure=[]) or there are no more elements without dependencies.
%
% For each element without dependencies, create a new norm, decrease the counters
% of the involved cost equations and  (try to) remove the elements where that element appears as
% a dependency


find_phase_upper_bounds(_Structure,[],_Phase_info,Concrete_norms,Concrete_norms):-!.
find_phase_upper_bounds([],_,_Phase_info,Concrete_norms,Concrete_norms):-!.
find_phase_upper_bounds([0-val(Loops,Rf,[],[],Accum)|Deps],Counters,Phase_info,Norms_accum,Norms):-!,
    update_ub_counters(Counters,Loops,Counters2),
    Norms_accum2=[norm(Loops,Rf+Accum)|Norms_accum],
	update_deps_ub_structure(Deps,Loops,Rf+Accum,Phase_info,Deps1),
	find_phase_upper_bounds(Deps1,Counters2,Phase_info,Norms_accum2,Norms).
find_phase_upper_bounds([N-val(Loop,Rf,Incr_Deps,Unknown_Deps,Accum)|Deps],Counters,Phase_info,Norms_accum,Norms):-
	N>0,
	keysort([N-val(Loop,Rf,Incr_Deps,Unknown_Deps,Accum)|Deps],[N2-val(Loop2,Rf2,Incr_Deps2,Unknown_Deps2,Accum2)|Deps2]),
	(N2=0->
	 find_phase_upper_bounds([N2-val(Loop2,Rf2,Incr_Deps2,Unknown_Deps2,Accum2)|Deps2],Counters,Phase_info,Norms_accum,Norms)
	;
	 Norms=Norms_accum
	).

%! update_ub_counters(+Counters:list_map(equation_id,int),+Loops:set_list(equation_id),-Counters2:list_map(equation_id,int)) is det
% remove one from the counters corresponding to the cost equations in Loops
% if a counter reaches 0, remove the pair from the map
update_ub_counters([],_,[]).
update_ub_counters(Counters,[],Counters):-!.
update_ub_counters([(Loop,N)|Cnts],[Loop|Loops],Counters):-!,
	N1 is N-1,
	(N1 > 0-> 
	   Counters=[(Loop,N1)|Counters_aux]
	   ;
	   Counters=Counters_aux
	   ),
	update_ub_counters(Cnts,Loops,Counters_aux).
update_ub_counters([(Loop,N)|Cnts],[Loop2|Loops],[(Loop,N)|Counters_aux]):-
	Loop < Loop2,!,
	update_ub_counters(Cnts,[Loop2|Loops],Counters_aux).	
	
update_ub_counters([(Loop,N)|Cnts],[Loop2|Loops],Counters_aux):-
	Loop > Loop2,
	update_ub_counters([(Loop,N)|Cnts],Loops,Counters_aux).		


%! update_deps_ub_structure(+Structure:rf_structure,+Loops_ub:set_list(equation_id),+Ub:cost_expression,+Phase_info:(term,phase,chain),-Structure_out:rf_structure) is det
% For each element in Structure:
%
% * Remove the increment dependencies to the loops in Loops_ub, obtain the maximum increment Max_incr
%   and add Max_inc* Ub to the accumulator
% * For the loops In Loops_ub that are unknown dependencies, 
%   try to find a reset value of the ranking function in that loop.
%   * If no reset is found, the dependency is not removed
%   * If we find a reset, we add max(Resets)* nat(Ub) to the accumulator
% * Finally, we recompute the number of dependencies
update_deps_ub_structure([],_,_,_,[]).
update_deps_ub_structure([_-val(Loops,Rf,Incr_Deps,Unknown_Deps,Accum)|Deps],Loops_ub,Ub,Phase_info,
                         [N2-val(Loops,Rf,Incr_Deps2,Unknown_Deps2,Accum2)|Desp1]):-
	remove_incr_loops(Incr_Deps,Loops_ub,Incr_Deps2,Max_incr),
	(Max_incr >0 -> 
	      Accum1=Accum+Max_incr* nat(Ub)
	      ;
	      Accum1=Accum
	 ),
	intersection_sl(Unknown_Deps,Loops_ub,Removable_Unknown_deps),
	find_resets(Removable_Unknown_deps,Rf,Phase_info,Removed_deps,Resets),
	(Resets\=[]->
	   Accum2=Accum1+max(Resets)* nat(Ub)
	   ;
	   Accum2=Accum1
	   ),
	difference_sl(Unknown_Deps,Removed_deps,Unknown_Deps2),
	
	length(Incr_Deps2,N2_1),
	length(Unknown_Deps2,N2_2),
	N2 is N2_1+N2_2,
	update_deps_ub_structure(Deps,Loops_ub,Ub,Phase_info,Desp1).


remove_incr_loops([],_Loops_ub,[],0).
remove_incr_loops([(Loop,N)|Incr_Deps],Loops_ub,Incr_Deps2,Max_incr):-
	contains_sl(Loops_ub,Loop),!,
	remove_incr_loops(Incr_Deps,Loops_ub,Incr_Deps2,Max_incr_aux),
	Max_incr is max(Max_incr_aux,N).
remove_incr_loops([(Loop,N)|Incr_Deps],Loops_ub,[(Loop,N)|Incr_Deps2],Max_incr):-
	remove_incr_loops(Incr_Deps,Loops_ub,Incr_Deps2,Max_incr).
	
% If Rf is reseted to a new value in an equation Dep, after Dep Rf will have a fixed value.
% We try to relate such value with the initial values of the variables at the beginning of the
% phase using phase_star

find_resets([],_,_Phase_info,[],[]).

find_resets([Dep|Deps],Rf,(Head,Phase,Chain),[Dep|Removed_deps],[Reset|Resets]):-	
	get_phase_star(Head,Call,Phase,Cs_star),
	loop_ph(Call,(Dep,_),Call2,Cs,_,_),
    nad_glb(Cs,Cs_star,Cs_total),
	Head=..[_|EVars],
	copy_term((Head,Rf),(Call2,Rf_instance)),
	max_min_linear_expression_all(Rf_instance,EVars,Cs_total,max,Rf_bounds),
	member(Reset,Rf_bounds),!,
	find_resets(Deps,Rf,(Head,Phase,Chain),Removed_deps,Resets).
	
find_resets([_Dep|Deps],Rf,Phase_info,Removed_deps,Resets):-	
	find_resets(Deps,Rf,Phase_info,Removed_deps,Resets).	