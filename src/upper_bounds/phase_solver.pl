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
						nad_consistent_constraints/1]).
:- use_module(stdlib(profiling),[profiling_start_timer/1,profiling_get_info/3,
				 profiling_stop_timer/2,profiling_stop_timer_acum/2]).
:- use_module(stdlib(counters),[counter_increase/3]).

%! phase_cost(Phase:phase,Head:term,Call:term,Forward_inv_hash:(int,polyhedron),Cost:cost_structure)
% store the cost structure of a phase given a local invariant
% for cacheing purposes
:- dynamic  phase_cost/5.

%! lex_ub(Head:term,Phase:phase,Eq_id:equation_id,Lex_ub:cost_expression)
% store an upper bound on the number of iterations of Eq_id in the the phase Phase.
% it has been computed taking into account ranking functions and their dependencies.
:-dynamic lex_ub/4.

%! init_phase_solver is det
% clear all the intermediate results
init_phase_solver:-
	retractall(phase_cost(_,_,_,_,_,_)),
	retractall(lex_ub(_,_,_,_)).

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
compute_phases_cost([Phase|More],Chain,Head,Call,[Cost1|Costs]):-
	copy_term(Head,Head_total),
	%get all kinds of invariants
	%backward_invariant(Head_total,(Chain,_),_,Head_patt),
	relation2entry_invariant(Head_total,([Phase|More],_),inv(Head_total,Head,Inv_cs)),
	forward_invariant(Head,([Phase|More],_),Forward_inv_hash,Forward_inv),
		
	(
	loop_ph(Head,(Phase,_),none,Phi,_,_)
	;
	(loop_ph(Head,(Phase,_),Call,Phi,_,_),Call\==none)
	;
	phase_loop(Phase,_,Head,Call,Phi)
	 ),!,
	%obtain a cost structure in terms of the variables at the beginning and end of the phase
	compute_phase_cost(Phase,Chain,Head,Call,(Forward_inv_hash,Forward_inv),Cost),	
	Head_total=..[_|Vars],
	%this is much cheaper than applying glb (at least in this case)
	%ut_flat_list([Phi,Inv_cs,Forward_inv,Head_patt],Cs_total),
	ut_flat_list([Phi,Inv_cs,Forward_inv],Cs_total),
	
	%solve the internal loops and express them in terms of the variables at the beginning of the chain
	max_min_internal_elements(Cost,Vars,Cs_total,Cost1),	
	Head_total=Head,
	compute_phases_cost(More,Chain,Head,Call,Costs).
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%! compute_phase_cost(Phase:phase,Head:term,Call:term,Forward_inv_hash:(int,polyhedron),Cost:cost_structure) is det
% Obtain the cost of a phase given a forward invariant.
% if the phase is non-iterative, the cost is the cost of the equation, otherwise:
% * get the cost of all the equations
% * put each cost into a new loop
% * try to take loops out by inductive compression
% * try to compress constraints from different loops
compute_phase_cost(Phase,_,Head,Call,(Forward_hash,Forward_inv),Cost):-
	phase_cost(Phase,Head,Call,(Forward_hash,Forward_inv2),Cost),
	Forward_inv2==Forward_inv,!,
	counter_increase(compressed_phases1,1,_).
% in a non-iterative phase, we just obtain the cost of the equation
compute_phase_cost(Non_it,_,Head,Call,Forward_inv_hash,Cost):-
	number(Non_it),
	profiling_start_timer(equation_cost),
	get_equation_cost(Head,Call1,Forward_inv_hash,Non_it,Cost),
	(Call1\=none->Call1=Call;true),
	profiling_stop_timer_acum(equation_cost,_),
	assert(phase_cost(Non_it,Head,Call,Forward_inv_hash,Cost)).

compute_phase_cost(Phase,Chain,Head,Call,Forward_inv_hash,cost(0,Loops2,Constrs3,IConstrs)):-
    %get the cost of each iterative component of the phase
	maplist(compute_phase_loop_cost(Head,Call,Forward_inv_hash),Phase,Loops),
	
	term_variables(Head,Head_vars),
	from_list_sl(Head_vars,Head_vars_set),
	term_variables(Call,Call_vars),
	from_list_sl(Call_vars,Call_vars_set),
	
	maplist(get_internal_norm_expressions((Call_vars_set,Head_vars_set)),Loops,Norm_exprs),
	maplist(get_loop_it_var,Loops,It_vars),
	add_rfs(Head,Call,Phase,Chain,It_vars,[],It_constrs,Differential_norms),
	%add_inverse_rfs(Head,Call,Phase,Chain,It_vars,[],IConstrs),
	IConstrs=[],

	profiling_start_timer(flatten_loops),
	inductive_compression(Head,Call,Phase,Norm_exprs,Compressed_norms),
	extract_unrolled_loops(Loops,Compressed_norms,Loops2,Unrolled_norms),
	profiling_stop_timer_acum(flatten_loops,_),
	%eliminate iteration variables with zero cost
	%simplify_or_cost_structure(Loops_out_flat,External_constrs,Cs_transitive,Removed_it_vars,Elems2,NormsList2),
	
	unions_sl([It_constrs,Differential_norms,Unrolled_norms],Constrs3),	
	assert(phase_cost(Phase,Head,Call,Forward_inv_hash,cost(0,Loops2,Constrs3,IConstrs))).

extract_unrolled_loops(Loops,Compressed_exps,Loops2,Unrolled_norms2):-
	maplist(extract_unrolled_loop_1(Compressed_exps),Loops,Loops_unrolled,Unrolled_norms),
	ut_flat_list(Loops_unrolled,Loops2),
	%FIMXE here!!!
	get_norm_combinations_greedy(Unrolled_norms,Unrolled_norms2).


get_norm_combinations_greedy(Norms,Gen_norms_set):-
	exclude(empty_list,Norms,Norms1),
	get_norm_combinations_greedy_1(Norms1,Gen_norms),
	from_list_sl(Gen_norms,Gen_norms_set).

get_norm_combinations_greedy_1([],[]).	
get_norm_combinations_greedy_1(Norms,[norm(Its,Exp)|Gen_norms]):-
	maplist(head_tail,Norms,[norm(Its_0,Exp)|Heads],Tails),
	exclude(empty_list,Tails,Tails1),
	foldl(accum_norm,Heads,norm(Its_0,Exp),norm(Its,Exp)),
	get_norm_combinations_greedy_1(Tails1,Gen_norms).

empty_list([]).
head_tail([H|T],H,T).
accum_norm(norm(Its_1,Exp),norm(Its_0,Exp),norm(Its,Exp)):-
	union_sl(Its_0,Its_1,Its).	
	
extract_unrolled_loop_1(Compressed_exps,loop(It_var,Base,Loops,Norms,INorms),[Loop|Loops_unrolled],Unrolled):-
	partition(norm_contains_exp(Compressed_exps),Norms,Unrolled,Remaining),
	%FIXME reinforce with It_var
	maplist(get_it_vars_in_constr,Unrolled,It_vars_list),
	unions_sl(It_vars_list,It_vars_set),
	clean_remaining_norms(Remaining,It_vars_set,Remaining1),
	clean_remaining_norms(INorms,It_vars_set,INorms_remaining),
	partition(is_loop_unrolled(It_vars_set),Loops,Loops_unrolled,Loops_left),
	Loop=loop(It_var,Base,Loops_left,Remaining1,INorms_remaining).
	
is_loop_unrolled(It_vars_set,loop(It_var,_Base,_Internal,_Norms,_INorms)):-
	contains_sl(It_vars_set,It_var).	
	
get_it_vars_in_constr(norm(Its,_L),Its_set):-
	from_list_sl(Its,Its_set).	

clean_remaining_norms([],_It_vars_set,[]).
clean_remaining_norms([Norm|Remaining],It_vars_set,Remaining1):-
	remove_it_vars_from_constr(It_vars_set,Norm,norm(Diff,Rf)),
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
%! compute_phase_loop_cost(+Head:term,+Call:term,+Forward_inv_hash:(int,polyhedron),+Cs_star_trans:polyhedron,+Cs_transitive:polyhedron,+Eq_id:equation_id,-It_var_Loops_out:(var,list(loop_cost)),-External_constrs2:list(norm)) is det
% given a cost equation id that belongs to a phase:
% * get the cost of the equation
% * put it inside a loop
% * try to compress their constraints inductively and extract the involved loops accordingly
compute_phase_loop_cost(Head,Call,Forward_inv_hash,Eq_id,loop(_It_var,Base,Elems,Constrs,IConstrs)):-
	profiling_start_timer(equation_cost),
	get_equation_cost(Head,Call,Forward_inv_hash,Eq_id,cost(Base,Elems,Constrs,IConstrs)),
	profiling_stop_timer_acum(equation_cost,_).

get_internal_norm_expressions(Call_vars_set,loop(_It_var,_Base,_Elems,Constrs,_IConstrs),Norm_exps_set):-
	maplist(get_norm_exp,Constrs,Norms_exps),
	include(contains_vars(Call_vars_set),Norms_exps,Norms_exps1),
	include(is_linear_exp,Norms_exps1,Linear_norms),
	from_list_sl(Linear_norms,Norm_exps_set).
	
get_norm_exp(norm(_,Exp),Exp).
norm_contains_exp(Exps,norm(_,Exp)):-
	contains_sl(Exps,Exp).	
	
contains_vars((Var_set1,Var_set2),Exp):-
	term_variables(Exp,Vs),
	from_list_sl(Vs,Vs_set),
	\+intersection_sl(Var_set1,Vs_set,[]),
	\+intersection_sl(Var_set2,Vs_set,[]).

get_loop_it_var(loop(It_var,_Base,_Elems,_Constrs,_IConstrs),It_var).

%! inductive_compression(+Loop:loop_cost,+Phi:polyhedron,+Head:term,+Cs_star_trans:polyhedron,+Cs_trans:polyhedron,+Call:term,-New_loops:list(loop_cost),-Unrolled_mult_set:list_set(norm)) is det
% * get the expressions in Norms and try to compress them inductively (unroll them)
% * split the  constraints into unrolled and not_unrolled.
% * get the interation variables that have been compressed and extract the involved loops
% * remove such iteration variables from the norms that are not unrolled
inductive_compression(Head,Call,Phase,Expressions_sets,Compressed_norms1):-
	phase_transitive_closure(Phase,_,Head,Call,Cs_transitive),
	unions_sl(Expressions_sets,All_expressions),	
	maplist(get_expressions_map(Expressions_sets,Phase),All_expressions,Expressions_map),
	maplist(tuple,All_expressions,Expressions_map,Pairs),
	%phase_loop(Phase,_,Head,Call,Phi),
	get_phase_star(Head,Call,Phase,Cs_star_trans),
	include(try_inductive_compression(Head,Cs_star_trans,Cs_transitive,Call),Pairs,Compressed_norms),
	maplist(tuple,Compressed_norms1,_,Compressed_norms).
	
get_expressions_map(Ex_sets,Phase,Exp,Map_flat):-
	maplist(loop_contains_exp(Exp),Ex_sets,Phase,Map),
	ut_flat_list(Map,Map_flat).
	
get_loop_cs(Head,Call,Loop,Cs):-
	loop_ph(Head,(Loop,_),Call,Cs,_,_).
	
loop_contains_exp(Exp,Set,Loop,[Loop]):-
		contains_sl(Set,Exp),!.
loop_contains_exp(_Exp,_Set,_Loop,[]).	
%! try_inductive_compression(+Head:term,+Phi:polyhedron,+Cs_star_trans:polyhedron,+Cs_trans:polyhedron,+Call:term,?L_Constant:(linear_expression,int)) is semidet
% try to compress a linear expression L inductively
% if succeed, The constant in the pair gives the extra decrement produced by Phi in L
try_inductive_compression(Head,Cs_star_trans,Cs_trans,Call,(L,Expressions_map)):-
	maplist(get_loop_cs(Head,Call),Expressions_map,Css),
	nad_list_lub(Css,Phi),
	
	copy_term((Head,Call,Cs_star_trans),(Call,Call2,Cs2)),
	copy_term((Head,Call,Phi,L),(Call2,Call3,Cs3,L2)),

	ut_flat_list([Cs_trans,Cs2,Cs3],Cs_comb),
	Head=..[_|EVars],
	Call3=..[_|ECall3],
	append(EVars,ECall3,Vars),

	term_variables((L,L2),Vars_constraint),
	slice_relevant_constraints_and_vars(Vars_constraint,Vars,Cs_comb,Vars1,Cs_comb1),
	
	max_min_linear_expression_all(L+L2,Vars1,Cs_comb1,max,Lsum_list),
	member(Lsum,Lsum_list),
	Call=Call3,%here Lsum and L are in the same universe
	max_min_linear_expression_all(Lsum-L,[],Cs_trans,max,Maxs),
	member(Constant,Maxs),
	Constant=<0,!.
	

%! reinforce_unrolled_constraint(+It_var,+Norm:norm,+Norm_info:int,-Norm_out:norm)
% if the norm_info is positive, we add the iteration variable of the main loop to the
% compressed norm
reinforce_unrolled_constraint(_,norm(Its,Rf),0,norm(Its,Rf)):-!.
reinforce_unrolled_constraint(It_var,norm(Its,Rf),C,norm(Its2,Rf)):-
	C>0,
	insert_sl(Its,It_var,Its2).





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