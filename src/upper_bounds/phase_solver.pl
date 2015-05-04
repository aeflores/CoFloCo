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
	backward_invariant(Head_total,(Chain,_),_,Head_patt),
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
	ut_flat_list([Phi,Inv_cs,Forward_inv,Head_patt],Cs_total),

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

compute_phase_cost(Phase,Chain,Head,Call,Forward_inv_hash,cost(0,Elems2,Constrs3,IConstrs)):-
	phase_transitive_closure(Phase,_,Head,Call,Cs_transitive),
	get_phase_star(Head,Call,Phase,Cs_star_trans),
    %get the cost of each iterative component of the phase
	maplist(compute_phase_loop_cost(Head,Call,Forward_inv_hash,Cs_star_trans,Cs_transitive),Phase,It_vars_Loops_out,External_constrs),
	maplist(tuple,It_vars,Loops_out,It_vars_Loops_out),
	ut_flat_list(Loops_out,Loops_out_flat),

	profiling_start_timer(compress_or),
	%eliminate iteration variables with zero cost
	simplify_or_cost_structure(Loops_out_flat,External_constrs,Cs_transitive,Removed_it_vars,Elems2,NormsList2),
    %add the constraints based on the ranking functions of the phase
	add_rfs(Head,Call,Phase,Chain,It_vars,Removed_it_vars,It_constrs,Differential_norms),
	add_inverse_rfs(Head,Call,Phase,Chain,It_vars,Removed_it_vars,IConstrs),
	split_out_dependent_constrs(NormsList2,Call,NormsList3,NormsList4),
	ut_flat_list([It_constrs|NormsList4],NormList4_flat),
	from_list_sl(NormList4_flat,NormList4_set),
	%compress contraints that have been inductively compressed with the ones added from the ranking functions
	compress_or_constraints([Differential_norms|NormsList3],Head,Call,max,Constrs1),
	profiling_stop_timer_acum(compress_or,_),
		
	union_sl(NormList4_set,Constrs1,Constrs3),	
	assert(phase_cost(Phase,Head,Call,Forward_inv_hash,cost(0,Elems2,Constrs3,IConstrs))).


%! compute_phase_loop_cost(+Head:term,+Call:term,+Forward_inv_hash:(int,polyhedron),+Cs_star_trans:polyhedron,+Cs_transitive:polyhedron,+Eq_id:equation_id,-It_var_Loops_out:(var,list(loop_cost)),-External_constrs2:list(norm)) is det
% given a cost equation id that belongs to a phase:
% * get the cost of the equation
% * put it inside a loop
% * try to compress their constraints inductively and extract the involved loops accordingly
compute_phase_loop_cost(Head,Call,Forward_inv_hash,Cs_star_trans,Cs_transitive,Eq_id,(It_var,Loops_out),External_constrs):-
	profiling_start_timer(equation_cost),
	get_equation_cost(Head,Call,Forward_inv_hash,Eq_id,Cost),
	loop_ph(Head,(Eq_id,_),Call,Phi,_,_),
	profiling_stop_timer_acum(equation_cost,_),
	put_in_loop(Cost,Loop,It_var),
	profiling_start_timer(flatten_loops),
	inductive_compression(Loop,Phi,Head,Cs_star_trans,Cs_transitive,Call,Loops_out,External_constrs),
	profiling_stop_timer_acum(flatten_loops,_).

%! inductive_compression(+Loop:loop_cost,+Phi:polyhedron,+Head:term,+Cs_star_trans:polyhedron,+Cs_trans:polyhedron,+Call:term,-New_loops:list(loop_cost),-Unrolled_mult_set:list_set(norm)) is det
% * get the expressions in Norms and try to compress them inductively (unroll them)
% * split the  constraints into unrolled and not_unrolled.
% * get the interation variables that have been compressed and extract the involved loops
% * remove such iteration variables from the norms that are not unrolled
inductive_compression(Loop,Phi,Head,Cs_star_trans,Cs_trans,Call,New_loops,Unrolled_mult_set):-
	Loop=loop(It_var,_,_,Norms,INorms),
	maplist(zip_with_op,_,_,Expressions,Norms),
	from_list_sl(Expressions,Expressions_set),
	maplist(tuple,Expressions_set,_,Map_expressions),
	include(try_inductive_compression(Head,Phi,Cs_star_trans,Cs_trans,Call),Map_expressions,Unrolled_tuples),
	partition(is_unrolled(Unrolled_tuples),Norms,Unrolled_norms,Not_unrolled),
    %build the new norms of the compressed expressions
	maplist(create_unrolled_norms(Unrolled_tuples),Unrolled_norms,Unrolled,Info_unrolled),

	maplist(get_it_vars_in_constr,Unrolled_norms,It_vars_non_flat),
	ut_flat_list(It_vars_non_flat,It_vars),
	from_list_sl(It_vars,It_vars_set),
	%extract loops whose iteration variable is in a compressed norm

	% if the loop decreases a compressed constraint we can add its interation variable to the compressed norms
	%FIXME, maybe we should check that
	maplist(reinforce_unrolled_constraint(It_var),Unrolled,Info_unrolled,Unrolled_mult),
	from_list_sl(Unrolled_mult,Unrolled_mult_set),
	
    %remove compressed iteration variables from norms that are not compressed
	maplist(remove_it_vars_from_constr(It_vars_set),Not_unrolled,Not_unrolled_filtered),
	exclude(empty_norm,Not_unrolled_filtered,Not_unrolled_filtered1),
	
	maplist(remove_it_vars_from_constr(It_vars_set),INorms,IConstrs_filtered),
	exclude(empty_norm,IConstrs_filtered,IConstrs_filtered1),
	extract_involved_loops(It_vars_set,Loop,Not_unrolled_filtered1,IConstrs_filtered1,New_loops).

%! try_inductive_compression(+Head:term,+Phi:polyhedron,+Cs_star_trans:polyhedron,+Cs_trans:polyhedron,+Call:term,?L_Constant:(linear_expression,int)) is semidet
% try to compress a linear expression L inductively
% if succeed, The constant in the pair gives the extra decrement produced by Phi in L
try_inductive_compression(Head,Phi,Cs_star_trans,Cs_trans,Call,(L,Constant2)):-
	is_linear_exp(L),
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
	Constant=<0,!,
	Constant2 is -Constant.
	
	
%! split_out_dependent_constrs(+NormsL:list(norm),-Call:term,DepNormsL:list(norm),-Non_depNormsL:list(norm)) is det
% split a set of norms NormsL into the ones that depend on the variables of Call
% and the ones that don't
split_out_dependent_constrs(NormsL,Call,DepNormsL,Non_depNormsL):-
	Call=..[_|Vars],
	from_list_sl(Vars,Vars_set),
	maplist(split_out_dependent_constrs_1(Vars_set),NormsL,DepNormsL,Non_depNormsL).
split_out_dependent_constrs_1(Vars_set,Norms,DepNorms,Non_depNorms):-
	partition(norm_contains_vars(Vars_set),Norms,DepNorms,Non_depNorms).

	
	
put_in_loop(cost(Base,Elems,Constrs,IConstrs),loop(It_var,Base,Elems,Constrs,IConstrs),It_var).

%! is_unrolled(+Exps_map:list_map(cost_expression,int),+Norm:norm) is semidet
is_unrolled(Exps_map,norm(_,Exp)):-
	lookup_lm(Exps_map,Exp,_).

get_it_vars_in_constr(norm(Its,_L),Its).


%! create_unrolled_norms(+Tuples:list_map(cost_expression,int),+Norm:norm,-Norm:norm,-Norm_info:int) is semidet
% for a given Norm, we consult the map Triples of cost expressions that can be compressed
% if the cost expression of the norm can be compressed, we create a norm for each expression that is an upper bound (they are stored in the map)
% for each norm created, a copy of the integer information is made so Norms and Norms_info have the same length
% and their relative possition indicates their correspondence
create_unrolled_norms(Tuples,norm(Its,Exp),norm(Its,Exp),Info):-
	lookup_lm(Tuples,Exp,Info).


%! remove_it_vars_from_constr(+It_vars_set:list_set(var),+Norm:norm,-Filtered_constr:norm) is det
%  remove the Iteration variables in It_vars_set from the norm Norm
remove_it_vars_from_constr(It_vars_set,norm(Its,Rf),norm(Difference,Rf)):-
	from_list_sl(Its,Its_set),
	difference_sl(Its_set,It_vars_set,Difference).


%! extract_involved_loops(+It_vars_set:list_set(var),+Loop:loop_cost,-Loops:list(loop_cost)) is det
% given a set of iteration variables that are in compressed constraints,
% extract their loops from Loop. These loops that were inside the main loop, now they are
% at the same level. Loops is the transformed original loop plus the ones extracted.
extract_involved_loops(It_vars_set,loop(It_var,Base,Elems,_,_),Unrolled_norms,INorms,[New_loop|Unrolled]):-
	partition(is_loop_unrolled(It_vars_set),Elems,Unrolled,Not_unrolled),
	New_loop=loop(It_var,Base,Not_unrolled,Unrolled_norms,INorms).

%! is_loop_unrolled(+It_vars_set:list_set,+Loop:loop_cos in the set It_vars_set
is_loop_unrolled(It_vars_set,loop(It_var,_Base,_Internal,_Norms,_INorms)):-
	contains_sl(It_vars_set,It_var).

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

%FIXME: we do not add this constraints yet
add_inverse_rfs(_Head,_Call,_Phase,_Chain,_It_vars,_Removed_it_vars,[]).


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