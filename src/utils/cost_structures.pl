/** <module> cost_structures

 This module implements the predicates that deal with
 cost structures.

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
    
    
    Cost structures are the main data stucture used to represent cost in CoFloCo.
    They can represent multiple polynomial upper and lower bounds that can be positive or negative.
    The internal representation of cost structures is the following:
    
   - Cstr=cost(Ub_fcons,Lb_fcons,Iconstrs,BSummands,Constant)
    where:
     * Ub_fcons:list(fconstr)
     * Lb_fcons:list(fconstr)
     * Itcons:list(iconstr)
     * BSummands:list((itvar,fraction))
     * BConstant:fraction
    
    The cost of cost structure cstr is the cost of BSummands+Constant such that the intermediate variables of BSummands
    satisfy the constraints in Ub_fcons,Lb_fcons and Itcons.
    
    There are two kind of bound constraints (bconstr) final constraints (fconstr) and intermediate constraints (iconstr):
    Both kinds have the form:
    -  bound(op,Exp,Bounded)
      where:
       * Op \in {ub,lb}
       * Bounded: list_set(itvar)
       * In a final constraint, Exp is a normalized linear expression (nlin_exp)
       * In an intermediate constraint, Exp is an abstract structured cost (astrexp)
     A constraint bound(op,Exp,Bounded) represents:
       *  sum(Bounded) =< Exp  if Op=ub
       *  sum(Bounded) >= Exp  if Op=lb
         
     
     Ub_FCons contains the final constraints with Op=ub
     Lb_FCons contains the final constraints with Op=lb
     Iconstrs contains all the intermediate constraints
     
     The iconstrs are kept sorted topologically. The order is given by the itvars that they define and the ones that they use
     A iconstr:=bound(op,Exp,Bounded) uses the itvars in Exp and defines the ones in Bounded
       def(iconstr)=Bounded
       uses(iconstr)=itvars(Exp)
       iconstr1 =< iconstr2 if intersection_sl(uses(iconstr2),def(iconstr1)) is not empty
     
    - Itvar: list(basic_identifiers) intermediate vars identifiers are a list of identifiers that allows to track
      the intermediate variable to the point of the analysis where it was created
        
    - astrexp: an abstract structured expression has the form:
      Astrexp=exp(Index_pos:index,Index_neg:index,Pstrexp_pos:pstrexp,Pstrexp_neg:pstrexp)
       Represents a cost "Pstrexp_pos-Pstrexp_neg". The intermediate variables have been substituted by prolog variables
       and the relation between the intermediate variables and the prolog variables is stored in Index_pos and Index_neg
    -index: list_map((it_var,Var))   
    -pstrexp: a plain structured cost  has the form:
       pstrexp:=add(list(summand))
       summand:=mult(list(factor))
       factor:= Var | max(list(Var)) | min(list(Var))
      
*/



:- module(cost_structures,[
		opposite_ub_lb/2,
		max_min_ub_lb/2,
		new_itvar/1,
		get_loop_itvar/2,
		is_ub_bconstr/1,
		fconstr_new/4,
		fconstr_new_inv/4,
		iconstr_new/4,
		bconstr_get_bounded/2,
		bconstr_annotate_bounded/2,
		bconstr_accum_bounded_set/3,
		astrexp_new/2,
		pstrexp_pair_add/3,
		pstrexp_pair_empty/1,
		cstr_empty/1,
		astrexp_to_cexpr/2,
		basic_cost_to_astrexp/4,
		cstr_from_cexpr/2,
		cstr_get_itvars/2,
		cstr_get_unbounded_itvars/2,
		cstr_extend_variables_names/3,
		itvar_recover_long_name/2,
		cstr_propagate_sums/4,
		cstr_join/3,
		cstr_or_compress/2,
		cstr_simplify/2,
		cstr_sort_iconstrs/4,
		cstr_simplify_for_solving/5]).
		
		
:- use_module(cofloco_utils,[
				ground_copy/2,
				zip_with_op/3,
				is_rational/1,
				sort_with/3,
				write_sum/2,
				write_product/2,
				tuple/3,
				get_all_pairs/3,
				normalize_constraint/2]).
:- use_module(structured_cost_expression,[strexp_simplify_max_min/2,strexp_to_cost_expression/2]).	
:- use_module(cost_expressions,[cexpr_simplify/3,is_linear_exp/1]).	
:- use_module(polyhedra_optimizations,[nad_entails_aux/3]).	
:- use_module('../IO/params',[get_param/2]).
:- use_module('../IO/output',[
	print_itvars_renaming/1,
	print_aux_exp/1,
	print_cost_structure/1,
	print_cycle_in_cstr_warning/0,
	print_removed_possibly_redundant_cstrs/1,
	print_removed_unresolved_cstrs_cycle/1, 
	print_joined_itvar_sets_message/1,
	print_removed_redundant_constr_message/2]).	
:- use_module('../bound_computation/cost_structure_solver',[cstr_maxminimization/5]).
:- use_module('../bound_computation/constraints_maximization',[max_min_linear_expression_all/5]).

:- use_module(stdlib(linear_expression),[
	parse_le/2,
	write_le/2,
	negate_le/2,
    is_constant_le/1,
	integrate_le/3,
	elements_le/2,
	constant_le/2]).	
:- use_module(stdlib(counters),[counter_initialize/2,counter_increase/3]).
:- use_module(stdlib(utils),[ut_flat_list/2]).	
:- use_module(stdlib(multimap),[put_mm/4,from_pair_list_mm/2,values_of_mm/3]).	
:- use_module(stdlib(list_map),[lookup_lm/3,delete_lm/3,insert_lm/4]).

:- use_module(stdlib(fraction)).
:- use_module(stdlib(fraction_list)).
:- use_module(stdlib(set_list),[
		difference_sl/3,
		remove_sl/3,
		contains_sl/2,
		from_list_sl/2,
		unions_sl/2,
		union_sl/3,
		insert_sl/3,
		intersection_sl/3]).



:-dynamic short_db/3.
:-dynamic short_db_no_list/3.
:-use_module(library(apply_macros)).
:-use_module(library(lists)).
:-use_module(library(terms)).
:-use_module(library(rbtrees)).




opposite_ub_lb(ub,lb).
opposite_ub_lb(lb,ub).

max_min_ub_lb(max,ub).
max_min_ub_lb(min,lb).

%predicates for intermediate variables
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%! new_itvar(Itvar:itvar) is det
% generate a fresh intermediate variable name
new_itvar(aux(Num)):-
	counter_increase(aux_vars,1,Num).
	
%! get_loop_itvar(Loop:loop_id,Itvar:itvar) is det
% get the itvar corresponding to a loop identifier
get_loop_itvar(Loop,it(Loop)).


%! annotate_itvar(Op:atom,Itvar:itvar,Var:op(itvar))
% wrap an intermediate variable inside Op
annotate_itvar(Op,Itvar,Var):-
	Var=..[Op,Itvar].

%! annotate_index_itvar(Op:atom,Index_elem:(itvar,Var),Index_elem1:(op(itvar),Var))
% wrap the left element of an index pair inside Op	
annotate_index_itvar(Op,(Name,Var),(Name1,Var)):-
	Name1=..[Op,Name].	

% predicates on bound constraints (bconstraints)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%! is_constant_bconstr(Bconstr:bconstr) is semidet
% succeeds if Bconstr is a final constraint with constant expression
is_constant_bconstr(bound(_Op,[]+_Cnt,_Bounded)).
	
%! is_inter_bconstr(Bconstr:bconstr) is semidet
% succeeds if Bconstr is an intermediate constraint
is_inter_bconstr(bound(_,exp(_,_,_,_),_)).

%! is_ub_bconstr(Bconstr:bconstr) is semidet
% succeeds if Bconstr has Op=ub
is_ub_bconstr(bound(ub,_,_)).

%! is_negative_fconstr(Fconstr:fconstr) is semidet
% succeeds if Fconstr contains a negative constant expression
is_negative_fconstr(bound(_,[]+N,_Bounded)):-
		leq_fr(N,0).

%! bconstr_get_bounded(Bconstr:bconstr,Bounded:list(it_var)) is det
% return the bounded intermediate variables of Bconstr
bconstr_get_bounded(bound(_,_,Bounded),Bounded).

bconstr_empty_bounded(bound(_,_,[])).

bconstr_bounds_multiple_itvars(bound(_,_,[_,_|_])).

%bconstr_accum_bounded_set(Bconstr:bconstr,Set:list_set(itvar),Set1:list_set(itvar)) is det
% add the bounded itvars of Bconstr to Set
bconstr_accum_bounded_set(bound(_,_,Bounded_set),Set,Set1):-
	union_sl(Bounded_set,Set,Set1).

%! fconstr_new(Bounded:list(itvar),Op:op,NLin_exp:nlin_exp,Fconstr:fconstr) is det
% create a new final constraint
fconstr_new(Bounded,Op,NLin_exp,bound(Op,NLin_exp,Bounded_set)):-
	from_list_sl(Bounded,Bounded_set).
fconstr_new_inv(NLin_exp,Op,Bounded,bound(Op,NLin_exp,Bounded)).


fconstr_lose_negative_constant(bound(Op,Coeffs+Cnt,Bounded),bound(Op,Coeffs+0,Bounded)):-
	leq_fr(Cnt,0),!.
fconstr_lose_negative_constant(bound(Op,Coeffs+Cnt,Bounded),bound(Op,Coeffs+Cnt,Bounded)).

%! iconstr_new(Astrexp:astrexp,Bounded:list(itvar),Op:op,Iconstr:iconstr) is det
% create a new intermediate constraint
iconstr_new(Astrexp,Op,Bounded,bound(Op,Astrexp,Bounded_set)):-
	from_list_sl(Bounded,Bounded_set).


%! bconstr_annotate_bounded(+Bconstr:bconstr,-Bconstr1:bconstr)
% annotate the intermediate variables of a Bconstr with ub or lb according to the operator Op of the constraint and their sign
bconstr_annotate_bounded(bound(Op,exp(Pos_index,Neg_index,Pos,Neg),Bounded),bound(Op,exp(Pos_index1,Neg_index1,Pos,Neg),Bounded_set)):-!,
	opposite_ub_lb(Op,Op_neg),
	maplist(annotate_itvar(Op),Bounded,Bounded1),
	from_list_sl(Bounded1,Bounded_set),
	maplist(annotate_index_itvar(Op),Pos_index,Pos_index1),
	maplist(annotate_index_itvar(Op_neg),Neg_index,Neg_index1).
bconstr_annotate_bounded(bound(Op,Top,Bounded),bound(Op,Top,Bounded_set)):-
	maplist(annotate_itvar(Op),Bounded,Bounded1),
	from_list_sl(Bounded1,Bounded_set).

%! bconstr_remove_bounded(Set:list_set(itvar),Bconstr:bconstr,Bconstr:bconstr)
%  remove the itvars in Set from bounded itvars of Bconstr
bconstr_remove_bounded(Set,bound(Op,Exp,Bounded_set),bound(Op,Exp,Bounded_set1)):-
	difference_sl(Bounded_set,Set,Bounded_set1).
	
% predicates on abstract structured expressions (astrexp)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	

%! astrexp_new_simple_itvar(Itvar:itvar,Astrexp:astrexp) is det
% create an abstract structured cost expression (astrexp) with as single positive itvar
astrexp_new_simple_itvar(Itvar,exp([(Itvar,Var)],[],add([mult([Var])]),add([]))).

astrexp_new(Pos-Neg,exp(Index_pos,Index_neg,Pos_pstrexp,Neg_pstrexp)):-
	pstrexp_new(Pos,Index_pos,Pos_pstrexp),
	pstrexp_new(Neg,Index_neg,Neg_pstrexp).
	
pstrexp_new(add(Summands),Index,add(Summands_var)):-
	pstrexp_summand(Summands,[],Index,Summands_var).
	
pstrexp_summand([],Index,Index,[]).
pstrexp_summand([mult(Summand)|Summands],Index_accum,Index,[mult(Factors_simplified)|Summands_var]):-
	partition(is_rational,Summand,Fractions,Factors),
	foldl(substitute_itvar_by_var,Factors,Factors_vars,Index_accum,Index_accum2),
	product_frl(Fractions,Product),
	((Product=1,Factors_vars\=[])->
	  Factors_vars=Factors_simplified
	  ;
	append(Factors_vars,[Product],Factors_simplified)
	),
	pstrexp_summand(Summands,Index_accum2,Index,Summands_var).

substitute_itvar_by_var(max(Itvars),max(Vars),Index,Index_out):-!,
	foldl(substitute_itvar_by_var,Itvars,Vars,Index,Index_out).
	
substitute_itvar_by_var(min(Itvars),min(Vars),Index,Index_out):-!,
	foldl(substitute_itvar_by_var,Itvars,Vars,Index,Index_out).	
	
substitute_itvar_by_var(Itvar,Var,Index,[(Itvar,Var)|Index]).


astrexp_to_cexpr(exp(Index1,Index2,add(Summands),add(Summands2)),Exp3):-
	pstrexp_to_cexpr(add(Summands),Exp1),
	pstrexp_to_cexpr(add(Summands2),Exp2),
	( Exp2==0 ->
	  Exp3=Exp1
	  ;
	  Exp3=Exp1-Exp2
	 ),
	%unify the names and the variables of the index
	maplist(tuple,X,X,Index1),
	maplist(tuple,X2,X2,Index2).
	
	
pstrexp_to_cexpr(add(Summands),Exp3):-
	maplist(write_product_1,Summands,Summands2),
	write_sum(Summands2,Exp3).



write_product_1(mult(List),Product):-
	write_product(List,Product).

pstrexp_pair_empty(add([])-add([])).

pstrexp_pair_add(add(Pos_summands1)-add(Neg_summands1),add(Pos_summands2)-add(Neg_summands2),add(Pos_summands)-add(Neg_summands)):-
	append(Pos_summands1,Pos_summands2,Pos_summands),
	append(Neg_summands1,Neg_summands2,Neg_summands).		
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! basic_cost_to_astrexp(BSummands,BConstant,Max_min,Final_constraint)
%generate an astrexp from the basic cost of a cost structure
basic_cost_to_astrexp(BSummands,BConstant,Max_min,Exp):-
	max_min_ub_lb(Max_min,Op),
	opposite_ub_lb(Op,Op_neg),
	generate_summands_from_bsummands(BSummands,Index_pos,Index_neg,Summands_pos,Summands_neg),
	maplist(annotate_index_itvar(Op),Index_pos,Index_pos1),
	maplist(annotate_index_itvar(Op_neg),Index_neg,Index_neg1),
	%add the constant
	(geq_fr(BConstant,0)->
		Exp=exp(Index_pos1,Index_neg1,add([mult([BConstant])|Summands_pos]),add(Summands_neg))
	;
		negate_fr(BConstant,BConstant_neg),
		Exp=exp(Index_pos1,Index_neg1,add(Summands_pos),add([mult([BConstant_neg])|Summands_neg]))
	).
	
	

% predicates on cost structures (cstr)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! cstr_empty(Cstr:cstr) is det
% generate a cost structure with 0 cost
cstr_empty(cost([],[],[],[],0)).



%! cstr_infinite(Cstr:cstr) is det
% generate a cost structure with infinite
cstr_infinite(cost([],[],[],[(Name,1)],0)):-
	new_itvar(Name).



%! cstr_from_cexpr(Cexp:cexp,Cstr:cstr) is det
% generate a cost structure from a cost expression
cstr_from_cexpr(N,cost([],[],[],[],N)):-
	ground(N),!.
cstr_from_cexpr(Exp,cost(Ub_fconstrs,Lb_fconstrs,[],[(Aux1,1),(Aux2,-1)],0)):-
	is_linear_exp(Exp),!,
	parse_le(Exp,Lin_exp),
	negate_le(Lin_exp,Lin_exp_negated),
	new_itvar(Aux1),
	new_itvar(Aux2),
	fconstr_new([Aux1],ub,Lin_exp,Ub_fconstr1),
	fconstr_new([Aux2],ub,Lin_exp_negated,Ub_fconstr2),
	Ub_fconstrs=[Ub_fconstr1,Ub_fconstr2],
	
	fconstr_new([Aux1],lb,Lin_exp,Lb_fconstr1),
	fconstr_new([Aux2],lb,Lin_exp_negated,Lb_fconstr2),
	Lb_fconstrs=[Lb_fconstr1,Lb_fconstr2].
	
cstr_from_cexpr(nat(Exp),cost(Ub_fconstrs,Lb_fconstrs,[],[(Aux1,1)],0)):-
	parse_le(Exp,Lin_exp),!,
	new_itvar(Aux1),
	fconstr_new([Aux1],ub,Lin_exp,Ub_fconstr1),
	fconstr_new([Aux1],lb,Lin_exp,Lb_fconstr1),
	Ub_fconstrs=[Ub_fconstr1],
	Lb_fconstrs=[Lb_fconstr1].
	
% we limit the input cost expressions to linear expressions
cstr_from_cexpr(Exp,_):-
	throw(invalid_cost_expression(Exp)).


%! cstr_get_components(+Costs:list(cstr),-Ub_fcons:list(list(fconstr)),-Lb_fcons:list(list(fconstr)),-Itcons:list(list(iconstr)),-BSummands:list(list(bsummands)),-BConstants:list(constant)) is det
% obtain lists of the components of a cost structure separated
cstr_get_components([],[],[],[],[],[]).
cstr_get_components([cost(Ub_fcons,Lb_fcons,Itcons,BSummands,BConstant)|Rest],[Ub_fcons|Ub_fcons_rest],[Lb_fcons|Lb_fcons_rest],[Itcons|Itcons_rest],[BSummands|BSummands_res],[BConstant|BConstant_rest]):-
	cstr_get_components(Rest,Ub_fcons_rest,Lb_fcons_rest,Itcons_rest,BSummands_res,BConstant_rest).
	
	
%! cstr_get_unbounded_itvars(+Cstr:cstr,-Unbounded:set(itvar)) is det
% compute a set of itvars that are not bound by any constraint
cstr_get_unbounded_itvars(cost(Top_exps,_LTop_exps,Aux_exps,Bases,_Base),Unbounded):-
      foldl(get_bounded_itvars(ub),Top_exps,[],Bounded_aux),
       foldl(get_bounded_itvars(ub),Aux_exps,Bounded_aux,Bounded),
       maplist(tuple,Itvars,_,Bases),
       from_list_sl(Itvars,Itvars_set),
       difference_sl(Itvars_set,Bounded,Unbounded).
get_bounded_itvars(Op,bound(Op,_,Bounded_set_new),Bounded_set,Bounded_set1):-!,
       union_sl(Bounded_set,Bounded_set_new,Bounded_set1).
get_bounded_itvars(_,_,Bounded_set,Bounded_set).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! cstr_simplify_for_solving(+Cstr:cstr,+Vars:list(var),+Phi:polyhedron,+Max_min:flag,-Cstr_simple:cstr)
% simplify the cost structure Cstr taking Phi into account
% Max_min_both can be 'max','min' or 'both' and indicates whether we want to obtain a maximum cost, minimum or both
cstr_simplify_for_solving(cost(Ub_fcons,Lb_fcons,Itcons,BSummands,BConstant),Vars,Phi,Max_min_both,Cstr_simple):-
	(get_param(solve_fast,[])->
		maplist(fconstr_lose_negative_constant,Ub_fcons,Ub_fcons2)
		;
		Ub_fcons2=Ub_fcons
	),
	Cstr=cost(Ub_fcons2,Lb_fcons,Itcons,BSummands,BConstant),
	cstr_simplify_fconstr_nats(Cstr,Vars,Phi,Cstr2),
	cstr_simplify_1(Cstr2,Max_min_both,Cstr3),
	Cstr3=Cstr_simple.

% simplify nat(linexp) that turn out to be zero	
cstr_simplify_fconstr_nats(Cstr,Vars,Phi,Cstr_simple):-
	Cstr=cost(Ub_fconstrs,Lb_fconstrs,Itcons,BSummands,BConstant),
	maplist(simplify_fconstr_nats(Vars,Phi),Ub_fconstrs,Ub_fconstrs1),
	maplist(simplify_fconstr_nats(Vars,Phi),Lb_fconstrs,Lb_fconstrs1),
	Cstr_simple=cost(Ub_fconstrs1,Lb_fconstrs1,Itcons,BSummands,BConstant).
	
simplify_fconstr_nats(Vars,Phi,bound(Op,Lin_exp,Bounded),bound(Op,[]+0,Bounded)):-
	integrate_le(Lin_exp,_Den,Lin_exp_nat),
	write_le(Lin_exp_nat,Expression_nat),
	nad_entails_aux(Vars,Phi,[Expression_nat =<0]),!.
	
simplify_fconstr_nats(_,_,Fconstr,Fconstr).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%! cstr_simplify(+Cost:cstr,-Cost_simple:cstr) is det
% join all the fconstr that have the same linear expression
% and simplify intermediate constraints:
%  - Discard redundant constraints i.e. if we have  it1+it2 =< A and it1 =< A, the second constraint is redundant
%  - Join intermediate variables that are subject to the same constraints
%  - remove contraints that depend on undefined itvars
%  - propagate nat(linexp) that turn out to be zero
%  - remove constraints that bound itvars that are not needed
cstr_simplify(Cstr,Cstr_final):-
	cstr_simplify_1(Cstr,both,Cstr_final).

cstr_simplify_1(cost(Ub_fcons,Lb_fcons,Itcons,Bsummands,BConstant),Max_min_both,Cstr_final):-
	(get_param(solve_fast,[])->
		maplist(ignore_negative_constants,Ub_fcons,Ub_fcons_aux),
		aggresively_simplify_ubconstrs(Ub_fcons_aux,Ub_fcons_aux2),
		aggresively_simplify_ubconstrs(Itcons,Itcons_aux)
	;
		Ub_fcons=Ub_fcons_aux2,
		Itcons=Itcons_aux
	),
	fconstr_join_equal_expressions(Ub_fcons_aux2,Ub_fcons2,Extra_itcons1),
	fconstr_join_equal_expressions(Lb_fcons,Lb_fcons2,Extra_itcons2),
	ut_flat_list([Extra_itcons1,Extra_itcons2,Itcons_aux],Itcons2),!,
	(get_param(solve_fast,[])->
		Itcons2=Itcons3
		;
		cstr_simplify_multiple_variables_constrs(Itcons2,Itcons3)
	),
	from_list_sl(Bsummands,Bsummands2),
	join_equivalent_itvars(cost(Ub_fcons2,Lb_fcons2,Itcons3,Bsummands2,BConstant),Cstr_aux2),
	cstr_remove_undefined(Cstr_aux2,Cstr_aux3),
	cstr_propagate_zeroes(Cstr_aux3,Cstr_aux4),
	cstr_remove_useless_constrs(Cstr_aux4,Max_min_both,Cstr_final),!.
	%cstr_count_appearances(Cstr_final).


aggresively_simplify_ubconstrs(Bconstrs,Bconstrs_split3):-
		maplist(split_bounds,Bconstrs,Bconstrs_aux),
		ut_flat_list(Bconstrs_aux,Bconstrs_split),

		length(Bconstrs,N1),
		length(Bconstrs_split,N2),
		(N2>N1->
		empty_setTree(Empty),
		foldl(remove_bconstr_duplicate,Bconstrs_split,(Empty,[]),(_,Bconstrs_split2)),
		reverse(Bconstrs_split2,Bconstrs_split3)
		;
		Bconstrs_split=Bconstrs_split3).

remove_bconstr_duplicate(Bconstr,(TreeSet,Accum),Res):-
	ground_copy(Bconstr,Bconstr_gr),
	term_hash(Bconstr_gr,Hash),
	(contains_setTree(TreeSet,(Hash,Bconstr_gr))->
		Res=(TreeSet,Accum)
		;
		insert_setTree(TreeSet,Hash,TreeSet1),
		Res=(TreeSet1,[Bconstr|Accum])
	).
		
split_bounds(bound(ub,Exp,[Bounded]),bound(ub,Exp,[Bounded])):-!.

split_bounds(bound(ub,Exp,Bounded),Fconstrs):-!,
	maplist(put_in_list,Bounded,Bounded_list),
	maplist(fconstr_new_inv(Exp,ub),Bounded_list,Fconstrs).
split_bounds(Bconstr,Bconstr).

ignore_negative_constants(bound(ub,Coeff+Cnt,Bounded),	bound(ub,Coeff+0,Bounded)):-
		leq_fr(Cnt,0),!.
ignore_negative_constants(bound(ub,Coeff+Cnt,Bounded),	bound(ub,Coeff+Cnt,Bounded)).


	
/*	
cstr_count_appearances(cost(Ub_fcons,Lb_fcons,Itcons,_Bsummands,_BConstant)):-
	rb_empty(Empty_tree),
	foldl(constr_count_appearances,Ub_fcons,Empty_tree,Appearances1),
	foldl(constr_count_appearances,Lb_fcons,Appearances1,Appearances2),
	foldl(constr_count_appearances,Itcons,Appearances2,Appearances3),
	rb_visit(Appearances3,Pair_list),
	include(one_occur,Pair_list,Pair_uni),
	length(Pair_uni,N),
	writeln(pairs(N,Pair_uni)).

one_occur(_-1).

constr_count_appearances(bound(_,_,Bounded),Appear_tree,Appear_tree1):-
	foldl(count_appearance,Bounded,Appear_tree,Appear_tree1).


count_appearance(Itvar,Appear_tree,Appear_tree1):-
	rb_apply(Appear_tree,Itvar,(increment),Appear_tree1),!.
count_appearance(Itvar,Appear_tree,Appear_tree1):-
	rb_insert(Appear_tree,Itvar,1,Appear_tree1).


increment(X,X1):-
	X1 is X+1.
*/	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%




%  Join intermediate variables that are subject to the same constraints	
% this is an incremental process, joining some itvars can make others equivalent
% we repeat it until we cannot merge anything else
join_equivalent_itvars(Cost,Cost2):-
	clean_right_sides,
	join_equivalent_itvars_1(Cost,Cost2).

join_equivalent_itvars_1(cost(Ub_fcons,Lb_fcons,Itcons,Bsummands,BConstant),cost(Ub_fcons,Lb_fcons,Itcons3,Bsummands3,BConstant)):-
	partition(bconstr_bounds_multiple_itvars,Itcons,Multiple_itconstrs,Single_itconstrs),
	% join the positive together and the negative together but do not mix them
	foldl(add_itvar_empty_map,Bsummands,[],Map_0),
	%Map_0=[],
	%create a multimap from itvars to hashes of right sides of iconstrs (or terms single(op,itvar) when the right side is a simple variable)
	% map(itvar,set(hash))

	foldl(get_itconstr_for_each_itvar,Single_itconstrs,Map_0,Map),
	% remove any itvar that is define by final constraints or constraints with several itvars
	foldl(remove_itvars_from_map,Ub_fcons,Map,Map1),
	foldl(remove_itvars_from_map,Lb_fcons,Map1,Map2),
	foldl(remove_itvars_from_map,Multiple_itconstrs,Map2,Map3),
	%reverse the multimap
	maplist(tuple,Itvar,Itconstr_set,Map3),
	maplist(tuple,Itconstr_set,Itvar,Map_inv),
	% list(set(hash),itvar)
	from_pair_list_mm(Map_inv,Multimap),
	% map(set(hash),set(itvar))
	% if some itvars are is only defined by itvar1 =< itvarN, itvar2 =< itvarN ... we can join itvar1,itvar2 and also itvarN
	get_unitary_pairs(Multimap,Itvar_multiple_sets1,Multimap2),
	maplist(tuple,_,Itvar_sets,Multimap2),
	% if some itvars are defined by the same right sides we can join them
	include(is_multiple_set,Itvar_sets,Itvar_multiple_sets2),	
	append(Itvar_multiple_sets1,Itvar_multiple_sets2,Itvar_multiple_sets),
	%Itvar_multiple_sets is a list(list_set(itvar))
	(Itvar_multiple_sets\=[]->
		print_joined_itvar_sets_message(Itvar_multiple_sets),
		join_itvar_sets(Itvar_multiple_sets,Itcons,Bsummands,Itcons2,Bsummands2),
		%try to simplify further
		join_equivalent_itvars_1(cost(Ub_fcons,Lb_fcons,Itcons2,Bsummands2,BConstant),cost(Ub_fcons,Lb_fcons,Itcons3,Bsummands3,BConstant))
		;
		Itcons3=Itcons,
		Bsummands3=Bsummands
	).

get_unitary_pairs([],[],[]).
get_unitary_pairs([([single(_Op,Itvar)],Itvar_set)|Multimap],[Itvar_set1|Itvar_sets],Multimap1):-!,
	Itvar_set1=[Itvar|Itvar_set],
	get_unitary_pairs(Multimap,Itvar_sets,Multimap1).
get_unitary_pairs([Pair|Multimap],Itvar_sets,[Pair|Multimap1]):-
	get_unitary_pairs(Multimap,Itvar_sets,Multimap1).	

add_itvar_empty_map((Itvar,Coeff),Map,Map1):-
	Coeff>0,!,
	insert_lm(Map,Itvar,[pos],Map1).
add_itvar_empty_map((Itvar,_),Map,Map1):-
	insert_lm(Map,Itvar,[neg],Map1).	
	
	
get_itconstr_for_each_itvar(bound(Op,Exp,[Itvar]),Map,Map1):-
	Exp=exp([(Itvar2,Var)],[],add([mult([Var])]),add([])),
	var(Var),!,
	put_mm(Map,Itvar,single(Op,Itvar2),Map1).

get_itconstr_for_each_itvar(bound(Op,Exp,[Itvar]),Map,Map1):-!,
	copy_term(Exp,Exp2),
	Exp2=exp(Index_pos,Index_neg,_,_),
	maplist(ground_index,Index_pos),
	maplist(ground_index,Index_neg),
	get_right_side_code((Op,Exp2),Code),
	put_mm(Map,Itvar,Code,Map1).


	
remove_itvars_from_map(bound(_,_,Bounded),Map,Map1):-
	foldl(delete_lm_aux,Bounded,Map,Map1).
	
delete_lm_aux(Key,Map,Map1):-
	delete_lm(Map,Key,Map1).
	
is_multiple_set([_,_|_]).	

%join_itvar_sets(+Sets:list(set_list(itvar)),+Itconstrs:list(iconstr),+Bsummands:list((itvar,fraction)),-Itconstrs_final:list(iconstr),-Bsummands_final:list((itvar,fraction))) is det
% if we have [a,|b,c] and [b|d] we want to substitute b by a in the second set
join_itvar_sets([],Itconstrs,Bsummands,Itconstrs,Bsummands).

join_itvar_sets([[Itvar|Equivalent_itvars]|Sets],Itconstrs,Bsummands,Itconstrs_final,Bsummands_final):-
	%get_first_appearance
	single_list_to_setTree(Equivalent_itvars,Equivalent_itvars_setTree),
	empty_setTree(Empty_Appeared),
	%keep the first appearance of each defining contraint, discard the rest
	keep_first_appearances(Itconstrs,Itvar,Equivalent_itvars_setTree,Empty_Appeared,Itconstrs2),
	empty_setTree(Empty_setTree),
	% substitute the uses of the Equivalent itvars by Itvar
	foldl(itconstr_substitute_itvars_in_exp(Itvar,Equivalent_itvars_setTree),Itconstrs2,(Empty_setTree,[]),(_,Itconstrs3)),
	reverse(Itconstrs3,Itconstrs4),
	% substitute the uses in the main expression
	compress_basic_summands(Bsummands,Itvar,Equivalent_itvars_setTree,Bsummands2),
	maplist(substitute_itvars_in_list(Itvar,Equivalent_itvars_setTree),Sets,Sets1),!,
	% next set of equivalent itvars
	join_itvar_sets(Sets1,Itconstrs4,Bsummands2,Itconstrs_final,Bsummands_final).

keep_first_appearances([],_,_,_,[]).

keep_first_appearances([bound(ub,exp([(Itvar2,Var)],[],add([mult([Var2])]),add([])),[Itvar3])|Itconstrs],Itvar,SetTree,Appeared,Itconstrs_final):-
	Var==Var2,
	(Itvar=Itvar2;contains_setTree(SetTree,Itvar2)),
	(Itvar=Itvar3;contains_setTree(SetTree,Itvar3)),!,
	keep_first_appearances(Itconstrs,Itvar,SetTree,Appeared,Itconstrs_final).

keep_first_appearances([bound(Op,Exp,[Itvar])|Itconstrs],Itvar,SetTree,Appeared,Itconstrs_final):-!,
	(contains_setTree(Appeared,bound(Op,Exp,[Itvar]))->
	    Itconstrs_final=Itconstrs2,
	    Appeared2=Appeared
	    ;
	    insert_setTree(Appeared,bound(Op,Exp,[Itvar]),Appeared2),
	    Itconstrs_final=[bound(Op,Exp,[Itvar])|Itconstrs2]
	),
	keep_first_appearances(Itconstrs,Itvar,SetTree,Appeared2,Itconstrs2).
	
keep_first_appearances([bound(Op,Exp,[Itvar2])|Itconstrs],Itvar,SetTree,Appeared,Itconstrs_final):-
	contains_setTree(SetTree,Itvar2),!,
	(contains_setTree(Appeared,bound(Op,Exp,[Itvar]))->
	    Itconstrs_final=Itconstrs2,
	    Appeared2=Appeared
	    ;
	    insert_setTree(Appeared,bound(Op,Exp,[Itvar]),Appeared2),
	    Itconstrs_final=[bound(Op,Exp,[Itvar])|Itconstrs2]
	),
	keep_first_appearances(Itconstrs,Itvar,SetTree,Appeared2,Itconstrs2).

keep_first_appearances([Other|Itconstrs],Itvar,SetTree,Appeared,[Other|Itconstrs2]):-
	keep_first_appearances(Itconstrs,Itvar,SetTree,Appeared,Itconstrs2).
	
single_list_to_setTree(List,Set):-
	maplist(make_trivial_pair,List,List_pair),
	list_to_rbtree(List_pair,Set).
make_trivial_pair(E,E-0).

empty_setTree(Empty):-
	rb_empty(Empty).

contains_setTree(Set,Elem):-
	rb_lookup(Elem,0,Set),!.
	
insert_list_setTree([],Set,Set).
insert_list_setTree([Elem|Elems],Set,Set_final):-
	rb_insert(Set, Elem, 0, Set1),
	insert_list_setTree(Elems,Set1,Set_final).
	
insert_setTree(Set,Elem,Set1):-
	rb_insert(Set, Elem, 0, Set1),!.

	
substitute_itvars_in_list(Itvar,Equivalent_itvars_setTree,List,[F|Set]):-
	maplist(substitute_itvar_in_list(Itvar,Equivalent_itvars_setTree),List,[F|List1]),
	from_list_sl(List1,Set).
	
substitute_itvar_in_list(Itvar,SetTree,Itvar2,Itvar):-
	contains_setTree(SetTree,Itvar2),!.	
substitute_itvar_in_list(_Itvar,_Set,Itvar2,Itvar2).


itconstr_substitute_itvars_in_exp(Itvar,Equiv_itvar_setTree,bound(Op,Exp,Bounded),(Bconstrs_hash_setTree,Bconstrs),Pair1):-
	%substitute occurrences of the equivalent itvars
	Exp=exp(Index_pos,Index_neg,Pos,Neg),
	maplist(substitute_itvars_in_index(Itvar,Equiv_itvar_setTree),Index_pos,Index_pos2),
	maplist(substitute_itvars_in_index(Itvar,Equiv_itvar_setTree),Index_neg,Index_neg2),
	Exp2=exp(Index_pos2,Index_neg2,Pos,Neg),
	copy_term(Exp2,Exp_ground),
	Exp_ground=exp(Index_pos_ground,Index_neg_ground,_,_),
	
	maplist(ground_index,Index_pos_ground),
	maplist(ground_index,Index_neg_ground),
	% only keep the iconstr if it is not repeated
	term_hash(bound(Op,Exp_ground,Bounded),Hash_new_bconstr),
	(contains_setTree(Bconstrs_hash_setTree,(Hash_new_bconstr,bound(Op,Exp_ground,Bounded)))->
		Pair1=(Bconstrs_hash_setTree,Bconstrs)
		;
		Bconstrs1=[bound(Op,Exp2,Bounded)|Bconstrs],
		insert_setTree(Bconstrs_hash_setTree,(Hash_new_bconstr,bound(Op,Exp_ground,Bounded)),Bconstrs_hash_setTree1),
		Pair1=(Bconstrs_hash_setTree1,Bconstrs1)
	).

substitute_itvars_in_index(Itvar,Equiv_itvar_setTree,(Itvar2,Var),(Itvar,Var)):-
	contains_setTree(Equiv_itvar_setTree,Itvar2),!.
substitute_itvars_in_index(_Itvar,_Equiv_itvar_setTree,(Itvar2,Var),(Itvar2,Var)).


compress_basic_summands(Bsummands,Itvar,Equivalent_itvars_setTree,Bsummands3):-
	reverse(Bsummands,Bsummands_rev),
	accum_equivalent_summands(Bsummands_rev,Itvar,Equivalent_itvars_setTree,[],0,Coeff_sum,Bsummands2),
	insert_lm(Bsummands2,Itvar,Coeff_sum,Bsummands3).


accum_equivalent_summands([],_Itvar,_Equivalent_itvars_setTree,Accum_summands,Accum_coeff,Accum_coeff,Accum_summands).
accum_equivalent_summands([(Itvar,Coeff)|Bsummands_rev],Itvar,Equivalent_itvars_setTree,Accum_summands,Accum_coeff,Coeff_sum,Bsummands_final):-!,
	sum_fr(Coeff,Accum_coeff,Accum_coeff2),
	accum_equivalent_summands(Bsummands_rev,Itvar,Equivalent_itvars_setTree,Accum_summands,Accum_coeff2,Coeff_sum,Bsummands_final).

accum_equivalent_summands([(Itvar2,Coeff)|Bsummands_rev],Itvar,Equivalent_itvars_setTree,Accum_summands,Accum_coeff,Coeff_sum,Bsummands_final):-
	contains_setTree(Equivalent_itvars_setTree,Itvar2),!,
	sum_fr(Coeff,Accum_coeff,Accum_coeff2),
	accum_equivalent_summands(Bsummands_rev,Itvar,Equivalent_itvars_setTree,Accum_summands,Accum_coeff2,Coeff_sum,Bsummands_final).	

accum_equivalent_summands([(Itvar2,Coeff)|Bsummands_rev],Itvar,Equivalent_itvars_setTree,Accum_summands,Accum_coeff,Coeff_sum,Bsummands_final):-
	accum_equivalent_summands(Bsummands_rev,Itvar,Equivalent_itvars_setTree,[(Itvar2,Coeff)|Accum_summands],Accum_coeff,Coeff_sum,Bsummands_final).	


ground_index((X,X)):-!.
ground_index(_).


% some predicates to assign codes to each right side of the iconstrs
:-dynamic right_side_code/3.

clean_right_sides:-
	retractall(right_side_code(_,_,_)),
	counter_initialize(right_side,0).

get_right_side_code(Rside,Code):-
	term_hash(Rside,Hash),
	right_side_code(Hash,Rside,Code),!.
	
get_right_side_code(Rside,Code):-
	term_hash(Rside,Hash),
	counter_increase(right_side,1,Code),
	assert(right_side_code(Hash,Rside,Code)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


 %! fconstr_join_equal_expressions(Fcons:list(fconstr),Fcons2:list(fconstr),New_Iconstrs:list(iconstr)) is det
 % group all final constraints that have the same expression and generate a single final constraint for each group
 % the original final constraints become intermediate constraints that reference the new final constraint
 fconstr_join_equal_expressions(Fcons,Fcons2,New_Iconstrs):-
	% create a multimap with the linear expression as a key and the final constraints as values
	foldl(add_fconstr_to_expr_fconstr_multimap,Fcons,[],Exp_Fcons_multimap),
	partition(unitary_multimap_entry,Exp_Fcons_multimap,Non_repeated_fconstrs_pairs,Repeated_fconstrs_pairs),
	maplist(tuple,_,Non_repeated_fconstrs,Non_repeated_fconstrs_pairs),
	% for each group (that corresponds to one linear expression)
	% that contains multiple final constraints, generate a final constraint and a list of intermediate constraints
	maplist(generate_compressed_fconstr,Repeated_fconstrs_pairs,New_fconstrs,New_Iconstrs),
	ut_flat_list([Non_repeated_fconstrs,New_fconstrs],Fcons2).

 %! add_fconstr_to_expr_fconstr_multimap(+Fconstr:fconstr,+Multimap:multimap(nlinexp,fconstr),-Multimap1:multimap(nlinexp,fconstr)) is det
 % add the pair (Exp,bound(Op,Exp,Bounded)) to the multimap
 add_fconstr_to_expr_fconstr_multimap(bound(Op,Exp,Bounded),Multimap,Multimap1):-
	put_mm( Multimap, Exp, bound(Op,Exp,Bounded), Multimap1).
	
 unitary_multimap_entry((_,[_])).

 %! generate_compressed_fconstr(Exp_Fcons:(nlinexp,list_set(fconstr)),New_fconstr:fconstr,New_iconstrs:list(itconstr)) is det
 % for each group Fcons,  generate a final constraint New_fconstr and a list of intermediate constraints New_iconstrs
 generate_compressed_fconstr((Exp,Fcons),New_fconstr,New_iconstrs):-
	Fcons=[bound(Op,_,_)|_],
	new_itvar(Name),
	fconstr_new([Name],Op,Exp,New_fconstr),
	maplist(fconstr_new_inv(_Exp,Op),Bounded_list,Fcons),
	(Op=ub->
		remove_redundant_bounded_sets(Bounded_list,Bounded_list2)
	;
	 	Bounded_list=Bounded_list2
	),
	astrexp_new_simple_itvar(Name,Astrexp),
	maplist(iconstr_new(Astrexp,Op),Bounded_list2,New_iconstrs).
	
	
remove_redundant_bounded_sets(Bounded_list,Bounded_list2):-
	sort_with(Bounded_list,bounded_size,Bounded_list_sorted),
	incrementally_remove_redundant_bounded(Bounded_list_sorted,[],Bounded_list2).
		
bounded_size(Bounded,Bounded2):-
        length(Bounded,N),
        length(Bounded2,N2),
        N<N2.


incrementally_remove_redundant_bounded([],Accum,Accum).
incrementally_remove_redundant_bounded([[One]|Ones],Accum,Result):-!,
	from_list_sl([[One]|Ones],Set),
	append(Accum,Set,Result).
incrementally_remove_redundant_bounded([Bounded|Bounded_list],Accum,Result):-
	exclude(is_redundant_bounded(Bounded),Bounded_list,Non_redundant),
	incrementally_remove_redundant_bounded(Non_redundant,[Bounded|Accum],Result).


is_redundant_bounded(Bounded,Bounded2):-
	difference_sl(Bounded2,Bounded,[]).	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%  Discard redundant constraints i.e. if we have  it1+it2 =< A and it1 =< A, the second constraint is redundant
cstr_simplify_multiple_variables_constrs(Itcons,Itcons2):-
	include(is_ub_bconstr,Itcons,Itcons_ub),
	sort_with(Itcons_ub,constr_more_bounded_vars,Itcons_sorted),
	empty_setTree(Empty_setTree),
	incrementally_remove_redundant_iconstrs(Itcons_sorted,Empty_setTree,Removed_setTree),
	exclude(contains_setTree(Removed_setTree),Itcons,Itcons2).

% order according to number of bounded itvars
 constr_more_bounded_vars(bound(_,_,Bounded),bound(_,_,Bounded2)):-
        length(Bounded,N),
        length(Bounded2,N2),
        N<N2.

%! incrementally_remove_redundant_iconstrs(+Constrs:list(iconstr),+Rem_etTree_accum:rbtree(iconstr,0),-Rem_etTree_accum:rbtree(iconstr,0)) is det
incrementally_remove_redundant_iconstrs([],Rem_setTree,Rem_setTree).
incrementally_remove_redundant_iconstrs([bound(ub,_Exp,[_])|_Constrs],Rem_setTree,Rem_setTree).
incrementally_remove_redundant_iconstrs([bound(ub,Exp,Bounded)|Constrs],Rem_setTree_accum,Rem_setTree):-
	partition(is_redundant(Exp,Bounded),Constrs,Removed_aux,Constrs1),
	print_removed_redundant_constr_message(bound(ub,Exp,Bounded),Removed_aux),
	insert_list_setTree(Removed_aux,Rem_setTree_accum,Rem_setTree_accum2),
	incrementally_remove_redundant_iconstrs(Constrs1,Rem_setTree_accum2,Rem_setTree).


is_redundant(Exp,Bounded,bound(ub,Exp2,Bounded2)):-
	ground_copy(Exp,Exp_gr),
	ground_copy(Exp2,Exp_gr),
	difference_sl(Bounded2,Bounded,[]).	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	
%! cstr_propagate_zeroes(+Cstr:cstr,-Cstr_simplified:cstr) is det
% simplify cost structure by eliminating final constraints with expressions that are guaranteed to be
% zero or smaller
% the intermediate variables that are upper bounded by one of these constraints are set to zero and the effect is propagated
% down to the basic summands	
cstr_propagate_zeroes(cost(Ub_fconstrs,Lb_fconstrs,Iconstrs,Bsummands,BConstant),Simplified):-
	partition(is_negative_fconstr,Ub_fconstrs,Removed_ub_fconstrs,Ub_fconstrs1),
	exclude(is_negative_fconstr,Lb_fconstrs,Lb_fconstrs1),	
	(Removed_ub_fconstrs\=[]->
	foldl(bconstr_accum_bounded_set,Removed_ub_fconstrs,[],Zero_set),
	propagate_zeroes_through_iconstrs(Iconstrs,Zero_set,Iconstrs2,Zero_set2),
	%remove the zeroes from the bounded of the lb_fconstrs
	maplist(bconstr_remove_bounded(Zero_set2),Lb_fconstrs1,Lb_fconstrs2),
	%check that there are no bconsts with 0 bounded itvars
	%FIXME
	exclude(bconstr_empty_bounded,Lb_fconstrs2,Lb_fconstrs3),
	exclude(bconstr_empty_bounded,Iconstrs2,Iconstrs3),
	exclude(pair_contains_first(Zero_set2),Bsummands,Bsummands1)
	;
	 Iconstrs3=Iconstrs,
	 Lb_fconstrs3=Lb_fconstrs1,
	 Bsummands1=Bsummands
	),
	Simplified=cost(Ub_fconstrs1,Lb_fconstrs3,Iconstrs3,Bsummands1,BConstant).

%! propagate_zeroes_through_iconstrs(Iconstrs:list(iconstr),Set:list_set(itvar),Iconstrs_out:list(iconstr),Set_out:list_set(itvar)) is det	
% propagate the intermediate variables that are zero (Set) and update any new itvars that are set to zero
propagate_zeroes_through_iconstrs([],Set,[],Set).
propagate_zeroes_through_iconstrs([bound(Op,Exp,Bounded_set)|Iconstrs],Set,Iconstrs_out,Set_out):-
	Exp=exp(Index_pos,Index_neg,Pos,Neg),
	partition(pair_contains_first(Set),Index_pos,Index_zero,Index_pos1),
	partition(pair_contains_first(Set),Index_neg,Index_zero_neg,Index_neg1),
	append(Index_zero,Index_zero_neg,Index_zero_total),
	Index_zero_total\=[],!,
	maplist(set_second_to(0),Index_zero_total),
	simplify_add(Pos,Pos1),
	simplify_add(Neg,Neg1),
	(Pos1=add([])->
	   Iconstrs_out=Iconstrs_out1,
	   union_sl(Bounded_set,Set,Set1)
	   ;
	   Exp1=exp(Index_pos1,Index_neg1,Pos1,Neg1),
	   bconstr_remove_bounded(Set,bound(Op,Exp1,Bounded_set),Iconstr),
	   Iconstrs_out=[Iconstr|Iconstrs_out1],
	   Set1=Set
	),
	propagate_zeroes_through_iconstrs(Iconstrs,Set1,Iconstrs_out1,Set_out).
	
propagate_zeroes_through_iconstrs([Iconstr1|Iconstrs],Set,[Iconstr2|Iconstrs_out],Set_out):-
	bconstr_remove_bounded(Set,Iconstr1,Iconstr2),
	propagate_zeroes_through_iconstrs(Iconstrs,Set,Iconstrs_out,Set_out).	  
	 
set_second_to(X,(_,X)).
simplify_add(add(Summands),add(Summands1)):-
    exclude(zero_summand,Summands,Summands1).
   
zero_summand(mult(Factors)):-
	member(F,Factors),
	F==0,!.	
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%/*

%cstr_sort_iconstrs(+Ub_fconstrs:list(fconstr),+Lb_fconstrs:list(fconstr),+Iconstrs:list(iconstr),-Iconstrs3:list(iconstr)) is det
% sort the Iconstrs topologically according to the itvars that they use and define
% there might be cycles in the iconstrs, in case a cycle is found, we remove "redundant" constraints
% that is, constraints that define itvars that have already been defined 
%
% even with that, it is possible that the cycle is not resolve, in which case we discard the remaining constraints
% FIXME: improve this
cstr_sort_iconstrs(Ub_fconstrs,Lb_fconstrs,Iconstrs,Iconstrs2):-
	foldl(bconstr_accum_bounded_set,Ub_fconstrs,[],Ub_Bounded_set),
	foldl(bconstr_accum_bounded_set,Lb_fconstrs,[],Lb_Bounded_set),
	%create pairs int:iconstr
	iconstrList_assign_ids(1,Iconstrs,Iconstrs_num),
	% create dependency graph between iconstr pairs (using predecessors)
	compute_iconstr_predecessor_graph(Iconstrs_num,Iconstrs_num,[],Pred_graph),
	%sort the iconstrs according to their dependencies
	get_topological_sorting(Pred_graph,(Ub_Bounded_set,Lb_Bounded_set),(Ub_Bounded_set,Lb_Bounded_set),Iconstrs2).

iconstrList_assign_ids(_N,[],[]).
iconstrList_assign_ids(N,[Iconstr|Iconstrs],[N:Iconstr|Iconstrs_num]):-
	N1 is N+1,
	iconstrList_assign_ids(N1,Iconstrs,Iconstrs_num).
	
compute_iconstr_predecessor_graph([],_All_Iconstrs,Map,Map).

compute_iconstr_predecessor_graph([N:Iconstr|Iconstrs],All_Iconstrs,Map_accum,Map):-
	include(is_pred_iconstr(Iconstr),All_Iconstrs,Pred),
	maplist(get_iconstr_id,Pred,Pred_ids),
	from_list_sl(Pred_ids,Pred_set),
	insert_lm(Map_accum,N:Iconstr,Pred_set,Map_accum2),
	compute_iconstr_predecessor_graph(Iconstrs,All_Iconstrs,Map_accum2,Map).

get_iconstr_id(N:_,N).

is_pred_iconstr(bound(ub,exp(Index,_Index_neg,_Exp,_Exp_neg),_),_N:bound(ub,_,Def_set)):-
	maplist(tuple,Names,_Vars,Index),
	from_list_sl(Names,Used_set),
	intersection_sl(Def_set,Used_set,[_|_]).
	
is_pred_iconstr(bound(lb,exp(_Index,Index_neg,_Exp,_Exp_neg),_),_N:bound(ub,_,Def_set)):-
	maplist(tuple,Names,_Vars,Index_neg),
	from_list_sl(Names,Used_set),
	intersection_sl(Def_set,Used_set,[_|_]).	

is_pred_iconstr(bound(lb,exp(Index,_Index_neg,_Exp,_Exp_neg),_),_N:bound(lb,_,Def_set)):-
	maplist(tuple,Names,_Vars,Index),
	from_list_sl(Names,Used_set),
	intersection_sl(Def_set,Used_set,[_|_]).		


%! get_topological_sorting(+Pred_graph:list(((int:iconstr),list(int))),+Bounded_itvars:list_set(itvar),-Iconstrs_final:list(iconstr)) is det
get_topological_sorting([],_,_,[]):-!.

get_topological_sorting(Pred_graph,Initially_bounded_itvars,Bounded_itvars,Iconstrs_final):-
	get_no_pred(Pred_graph,Iconstrs,Iconstrs_ids,Pred_graph2),
	(Iconstrs\=[]->
		from_list_sl(Iconstrs_ids,Iconstrs_ids_set),
		maplist(remove_preds(Iconstrs_ids_set),Pred_graph2,Pred_graph3),
		foldl(accum_bounded_itvars,Iconstrs,Bounded_itvars,Bounded_itvars2),
		get_topological_sorting(Pred_graph3,Initially_bounded_itvars,Bounded_itvars2,Iconstrs2),
		append(Iconstrs,Iconstrs2,Iconstrs_final)
		;
		%there is a cycle in the graph
		% we try to get rid of it by removing constraints that bound itvars that are already bound
		%FIXME: this could be improved
		print_cycle_in_cstr_warning,
		remove_redundant_constraints(Pred_graph2,Initially_bounded_itvars,Pred_graph3,[],Redundant_ids_set,[],Removed_iconstrs),
		(Redundant_ids_set=[] ->
				remove_redundant_constraints(Pred_graph2,Bounded_itvars,Pred_graph4,[],Redundant_ids_set2,[],Removed_iconstrs2)
				;
				Redundant_ids_set2=Redundant_ids_set,
				Removed_iconstrs2=Removed_iconstrs,
				Pred_graph4=Pred_graph3
		),	
		(Redundant_ids_set2\=[]->
			print_removed_possibly_redundant_cstrs(Removed_iconstrs2),
			%if we have removed something, we try to continue
			maplist(remove_preds(Redundant_ids_set2),Pred_graph4,Pred_graph5),
			get_topological_sorting(Pred_graph5,Initially_bounded_itvars,Bounded_itvars,Iconstrs_final)
			;
			%we fail to get rid of the cycle, we discard the remaining iconstrs
			print_removed_unresolved_cstrs_cycle(Pred_graph2),
			Iconstrs_final=[]
			)
	).
	
remove_redundant_constraints([],_Bounded_itvars,[],Removed_accum,Removed_accum,Removed_iconstrs,Removed_iconstrs).

remove_redundant_constraints([(Id:bound(ub,Exp,Bounded_set),_Preds)|Map],(Ub_set,Lb_set),Map_final,Removed_accum,Removed,Removed_iconstrs_accum,Removed_iconstrs):-
	difference_sl(Bounded_set,Ub_set,[]),!,
	insert_sl(Removed_accum,Id,Removed_accum2),
	remove_redundant_constraints(Map,(Ub_set,Lb_set),Map_final,Removed_accum2,Removed,[bound(ub,Exp,Bounded_set)|Removed_iconstrs_accum],Removed_iconstrs).
	
remove_redundant_constraints([(Id:bound(lb,Exp,Bounded_set),_Preds)|Map],(Ub_set,Lb_set),Map_final,Removed_accum,Removed,Removed_iconstrs_accum,Removed_iconstrs):-
	difference_sl(Bounded_set,Lb_set,[]),!,
	insert_sl(Removed_accum,Id,Removed_accum2),
	remove_redundant_constraints(Map,(Ub_set,Lb_set),Map_final,Removed_accum2,Removed,[bound(lb,Exp,Bounded_set)|Removed_iconstrs_accum],Removed_iconstrs).	
	
remove_redundant_constraints([Pair|Map],Bounded_itvars,[Pair|Map_final],Removed_accum,Removed,Removed_iconstrs_accum,Removed_iconstrs):-
	remove_redundant_constraints(Map,Bounded_itvars,Map_final,Removed_accum,Removed,Removed_iconstrs_accum,Removed_iconstrs).	
	

% get iconstrs with no predecessors
get_no_pred([],[],[],[]).
get_no_pred([(Iconstr_id:Iconstr,[])|Map],[Iconstr|Iconstrs],[Iconstr_id|Iconstrs_ids],Map_out):-!,
	get_no_pred(Map,Iconstrs,Iconstrs_ids,Map_out).
get_no_pred([Other|Map],Iconstrs,Iconstr_ids,[Other|Map_out]):-
	get_no_pred(Map,Iconstrs,Iconstr_ids,Map_out).	

%remove predecessors 	
remove_preds(Pred_set,(Iconstr,Set),(Iconstr,Set2)):-
	difference_sl(Set,Pred_set,Set2).
	
		
accum_bounded_itvars(bound(ub,_,Bounded_set),(Ub_accum,Lb_Bounded_set),(Ub_Bounded_set,Lb_Bounded_set)):-
	union_sl(Bounded_set,Ub_accum,Ub_Bounded_set).
	
accum_bounded_itvars(bound(lb,_,Bounded_set),(Ub_Bounded_set,Lb_accum),(Ub_Bounded_set,Lb_Bounded_set)):-
	union_sl(Bounded_set,Lb_accum,Lb_Bounded_set).	
	
%! cstr_remove_undefined(+Cost:cstr,-Short:cstr) is det
% Given a cost structure where the Iconstrs are topologically sorted, it filters out the ones that are not well defined (they depend on an itvar that is not defined)
cstr_remove_undefined(cost(Ub_fconstrs,Lb_fconstrs,Iconstrs,Bsummands,BConstant),cost(Ub_fconstrs,Lb_fconstrs,Bounded,Bsummands,BConstant)):-
	foldl(bconstr_accum_bounded_set,Ub_fconstrs,[],Ub_Bounded_set),
	foldl(bconstr_accum_bounded_set,Lb_fconstrs,[],Lb_Bounded_set),
	split_bounded(Iconstrs,Ub_Bounded_set,Lb_Bounded_set,_,_,Bounded,_).
	  
split_bounded([],Ub_Set,Lb_Set,Ub_Set,Lb_Set,[],[]).

split_bounded([bound(ub,exp(Index,Index_neg,Exp,Exp_neg),Bounded_set)|Iconstrs],Ub_Set,Lb_Set,Ub_Set_out,Lb_Set_out,[bound(ub,exp(Index,Index_neg,Exp,Exp_neg),Bounded_set)|Exp_Bounded],Exp_Not_bounded):-
	% the positive summands have to be well defined
	maplist(tuple,Names,_Vars,Index),
	maplist(contains_sl(Ub_Set),Names),!,
	%include Bounded_set into the Ub_set
	union_sl(Bounded_set,Ub_Set,Ub_Set_aux),
	split_bounded(Iconstrs,Ub_Set_aux,Lb_Set,Ub_Set_out,Lb_Set_out,Exp_Bounded,Exp_Not_bounded).


split_bounded([bound(lb,exp(Index,Index_neg,Exp,Exp_neg),Bounded_set)|Iconstrs],Ub_Set,Lb_Set,Ub_Set_out,Lb_Set_out,[bound(lb,exp(Index,Index_neg,Exp,Exp_neg),Bounded_set)|Exp_Bounded],Exp_Not_bounded):-
	% the negative summands have to be well defined
	maplist(tuple,Names,_,Index),
	maplist(contains_sl(Lb_Set),Names),
	maplist(tuple,Names_neg,_,Index_neg),
	maplist(contains_sl(Ub_Set),Names_neg),!,
	%include Bounded_set into the Lb_set
	union_sl(Bounded_set,Lb_Set,Lb_Set_aux),
	split_bounded(Iconstrs,Ub_Set,Lb_Set_aux,Ub_Set_out,Lb_Set_out,Exp_Bounded,Exp_Not_bounded).	
	
% Iconstr is not well defined
split_bounded([Iconstr|Iconstrs],Ub_Set,Lb_Set,Ub_Set_out,Lb_Set_out,Exp_Bounded,[Iconstr|Exp_Not_bounded]):-
	split_bounded(Iconstrs,Ub_Set,Lb_Set,Ub_Set_out,Lb_Set_out,Exp_Bounded,Exp_Not_bounded).



%! cstr_remove_useless_constrs(+Cost:cstr,Max_min_both:flag,-Cost_simple:cstr) is det
% Remove bound constraints that bound itvars that are not needed for the cost
% Max_min_both can be 'max','min' or 'both' and indicates whether we want to obtain a maximum cost, minimum or both
cstr_remove_useless_constrs(cost(Ub_fconstrs,Lb_fconstrs,Iconstrs,Bsummands,BConstant),Max_min_both,cost(Ub_fconstrs2,Lb_fconstrs2,Iconstrs2,Bsummands2,BConstant)):-
	(Max_min_both=both->
		foldl(compute_initial_reference_set(max),Bsummands,([],[]),(Bsummands1,Ref_set_aux)),
	    foldl(compute_initial_reference_set(min),Bsummands1,([],Ref_set_aux),(Bsummands2,Ref_set))
	    ;
	    foldl(compute_initial_reference_set(Max_min_both),Bsummands,([],[]),(Bsummands2,Ref_set))
	),
	reverse(Iconstrs,Aux_rev),
	remove_useless_iconstrs(Aux_rev,Ref_set,[],Ref_set1,Iconstrs2),
	exclude(is_fconstr_useless(Ref_set1),Ub_fconstrs,Ub_fconstrs2),
	exclude(is_fconstr_useless(Ref_set1),Lb_fconstrs,Lb_fconstrs2).

	
compute_initial_reference_set(_,(_Name,0),(Bsummands,Ref_set),(Bsummands,Ref_set)).
compute_initial_reference_set(min,(Name,Value),(Bsummands,Ref_set),([(Name,Value)|Bsummands],Ref_set2)):-
	(greater_fr(Value,0)->
		insert_sl(Ref_set,lb(Name),Ref_set2)
		;
		insert_sl(Ref_set,ub(Name),Ref_set2)
		).
compute_initial_reference_set(max,(Name,Value),(Bsummands,Ref_set),([(Name,Value)|Bsummands],Ref_set2)):-
	(greater_fr(Value,0)->
		insert_sl(Ref_set,ub(Name),Ref_set2)
		;
		insert_sl(Ref_set,lb(Name),Ref_set2)
		).	

remove_useless_iconstrs([],Ref_set,Iconstrs,Ref_set,Iconstrs).
remove_useless_iconstrs([bound(Op,Exp,Bounded)|Iconstrs],Ref_set_accum,Iconstrs_accum,Ref_set,Iconstrs_out):-
	opposite_ub_lb(Op,Op_neg),
	maplist(zip_with_op(Op),Bounded,Bounded_op),	
	from_list_sl(Bounded_op,Bounded_set),
	(Op=ub->
	intersection_sl(Ref_set_accum,Bounded_set,Bounded1_op),
	Bounded1_op\=[]
	;
	intersection_sl(Ref_set_accum,Bounded_set,Bounded_set),
	Bounded1_op=Bounded_set
	),!,
	maplist(zip_with_op(Op),Bounded1,Bounded1_op),
	Exp=exp(Index,Index_neg,_,_),
	add_elements_from_index(Op,Index,Ref_set_accum,Ref_set_accum1),
	add_elements_from_index(Op_neg,Index_neg,Ref_set_accum1,Ref_set_accum2),
	remove_useless_iconstrs(Iconstrs,Ref_set_accum2,[bound(Op,Exp,Bounded1)|Iconstrs_accum],Ref_set,Iconstrs_out).


remove_useless_iconstrs([_|Iconstrs],Ref_set_accum,Iconstrs_accum,Ref_set,Iconstrs_out):-	
	remove_useless_iconstrs(Iconstrs,Ref_set_accum,Iconstrs_accum,Ref_set,Iconstrs_out).		

	
add_elements_from_index(Op,Index,Set,Set1):-
	maplist(tuple,Names,_,Index),
	maplist(zip_with_op(Op),Names,Names_op),
	from_list_sl(Names_op,Names_set),
	union_sl(Names_set,Set,Set1).

is_fconstr_useless(Ref_set,bound(Op,_,Bounded)):-
	maplist(zip_with_op(Op),Bounded,Bounded_op),	
	from_list_sl(Bounded_op,Bounded_set),
	(Op=ub->
	intersection_sl(Bounded_set,Ref_set,[])
	;
	\+intersection_sl(Bounded_set,Ref_set,Bounded_set)
	).
		

	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! cstr_extend_variables_names(+Cost:cstr,+Prefix:term,-Cost_extended:cstr) is det
% generate a new instance of a cost structure by extending all itvar names with the Prefix
cstr_extend_variables_names(cost(Ub_fconstrs,Lb_fconstrs,Iconstrs,Bsummands,BConstant),Prefix,cost(Ub_fconstrs1,Lb_fconstrs1,Iconstrs1,Bsummands1,BConstant)):-
		maplist(fconstr_extend_name(Prefix),Ub_fconstrs,Ub_fconstrs1),
		maplist(fconstr_extend_name(Prefix),Lb_fconstrs,Lb_fconstrs1),
		maplist(iconstr_extend_name(Prefix),Iconstrs,Iconstrs1),
		maplist(bfactor_extend_name(Prefix),Bsummands,Bsummands1),
		print_itvars_renaming(cost(Ub_fconstrs1,Lb_fconstrs1,Iconstrs1,Bsummands1,BConstant)).
		


iconstr_extend_name(Prefix,bound(Op,Exp,Bounded),bound(Op,Exp1,Bounded_set)):-
	astrexp_extend_name(Prefix,Exp,Exp1),
	maplist(itvar_extend_name(Prefix),Bounded,Bounded2),
	from_list_sl(Bounded2,Bounded_set).
	
fconstr_extend_name(Prefix,bound(Op,Expression,Bounded),bound(Op,Expression,Bounded_set)):-
	maplist(itvar_extend_name(Prefix),Bounded,Bounded2),
	from_list_sl(Bounded2,Bounded_set).
	
astrexp_extend_name(Prefix,exp(Index,Index_neg,Exp,Exp_neg),exp(Index2,Index_neg2,Exp,Exp_neg)):-
	maplist(bfactor_extend_name(Prefix),Index,Index2),
	maplist(bfactor_extend_name(Prefix),Index_neg,Index_neg2).	
	
bfactor_extend_name(Prefix,(Name,Value),(Name2,Value)):-
	itvar_extend_name(Prefix,Name,Name2).

itvar_extend_name(Prefix,Name,Name2):-
	short_db(Name,Prefix,Name2),!.
itvar_extend_name(Prefix,Name,s(Name2)):-
	counter_increase(short_terms,1,Name2),
	assertz(short_db(Name,Prefix,s(Name2))).



itvar_recover_long_name(Name,(Prefix,Old)):-
	short_db(Old,Prefix,Name),!.
itvar_recover_long_name(Name,Name).

cstr_get_itvars(cost(Ub_fconstrs,Lb_fconstrs,Iconstrs,Bsummands,_),Set5):-
	maplist(tuple,Itvars,_,Bsummands),
	from_list_sl(Itvars,Set1),
	foldl(get_bounded_itvars(ub),Ub_fconstrs,Set1,Set2),
	foldl(get_bounded_itvars(lb),Lb_fconstrs,Set2,Set3),
	foldl(get_bounded_itvars(ub),Iconstrs,Set3,Set4),
	foldl(get_bounded_itvars(lb),Iconstrs,Set4,Set5).


 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	

%! cstr_join(+Cost1:cstr,+Cost2:cstr,-Cost3:cstr) is det
% join Cost1 and Cost2 into Cost3
cstr_join(cost(T,A,Iconstrs,Bs,B),cost(T2,A2,Iconstrs2,B2s,B2),cost(T3,A3,Iconstrs3,B3s,B3)):-
	append(T,T2,T3),
	append(A,A2,A3),
	append(Iconstrs,Iconstrs2,Iconstrs3),
	append(Bs,B2s,B3s),
	sum_fr(B,B2,B3).	
	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! cstr_propagate_sums(+Loop:loop_id,+Cost:cstr,-Cost2:cstr,-Max_mins:list(fconstr),-Summs:list(fconstr)) is det
% propagate the sum of a cost structure all form the basic summands to the final constraints
%
% Cost_out contains the transformed cost except the final constraints that still have to be computed
% Max_mins is a pair of set of final constraints that have to be maximized and minimized
% Sums is a pair of set of final constraints whose sum over Loop has to be computed
cstr_propagate_sums(Loop,cost(Ub_fconstrs,Lb_fconstrs,Iconstrs,Bsummands,BConstant),Cost2,(Max_mins,Sums)):-
	%transform the basic summands into sums and record the relation between the original variable and the sum variable in Sum_map_initial
	foldl(generate_initial_sum_map(Loop),Bsummands,Bsummands1,[],Sum_map_initial),
	get_loop_itvar(Loop,Itvar),
	propagate_sums_backwards(Iconstrs,Loop,Sum_map_initial,Iconstrs2,Sum_map,Max_min_set),
	Cost2=cost([],[],Iconstrs2,[(Itvar,BConstant)|Bsummands1],0),
	% get the final constraints that have to be computed
	foldl(get_maxs_mins(Max_min_set),Ub_fconstrs,[],Max_mins1),
	foldl(get_sums(Sum_map),Ub_fconstrs,[],Sums1),
	foldl(get_maxs_mins(Max_min_set),Lb_fconstrs,Max_mins1,Max_mins),
	foldl(get_sums(Sum_map),Lb_fconstrs,Sums1,Sums).



generate_initial_sum_map(_Loop,(Name,Val),(Name2,Val),Map,Map):-
	lookup_lm(Map,Name,Name2),!.
generate_initial_sum_map(Loop,(Name,Val),(Name2,Val),Map,Map1):-
	itvar_extend_name(sum(Loop),Name,Name2),
	insert_lm(Map,Name,Name2,Map1).

		
put_in_list(X,[X]).
	

get_maxs_mins(Max_min_set,bound(ub,Exp,Bounded),Bconstrs,Bconstrs2):-
	include(contains_sl(Max_min_set),Bounded,Non_summatories),
	maplist(put_in_list,Non_summatories,Unitary_bounded),
	maplist(iconstr_new(Exp,ub),Unitary_bounded,New_bounds),
	append(New_bounds,Bconstrs,Bconstrs2).
	
	
get_maxs_mins(Max_min_set,bound(lb,Exp,[One_Bounded]),Bconstrs,Bconstrs2):-
	contains_sl(Max_min_set,One_Bounded),!,
	Bconstrs2=[bound(lb,Exp,[One_Bounded])|Bconstrs].

get_maxs_mins(_Max_min_set,bound(lb,_Exp,_Bounded),Bconstrs,Bconstrs).
%	(include(contains_sl(Max_set),Bounded,Bounded)->
%	format(user_error,'Lost constraint ~p~n',[bound(lb,Exp,Bounded)])
%	;
%	true),

	
get_sums(Sum_map,bound(ub,Exp,Bounded),Bconstrs,Bconstrs2):-
	get_mapped(Bounded,Sum_map,New_names),
	New_names\=[],!,
	Bconstrs2=[bound(ub,Exp,New_names)|Bconstrs].
	
get_sums(Sum_map,bound(lb,Exp,Bounded),Bconstrs,Bconstrs2):-
	get_mapped(Bounded,Sum_map,New_names),
	length(Bounded,N),
	%only of we can keep all (all bounded are interesting)
	length(New_names,N),!,
	Bconstrs2=[bound(lb,Exp,New_names)|Bconstrs].
	
get_sums(_Sum_map,_,Bconstrs,Bconstrs).


propagate_sums_backwards(Iconstrs,Loop,Sum_map_initial,Iconstrs2,Sum_map,Max_min_set):-
	reverse(Iconstrs,Iconstrs_rev),
	foldl(propagate_sums(Loop),Iconstrs_rev,([],[],Sum_map_initial),(Iconstrs2,Max_min_set,Sum_map)).

propagate_sums(Loop,bound(Op,Astrexp,Bounded),(Iconstrs,Max_min_set,Sum_map),(Iconstrs3,Max_min_set4,Sum_map3)):-	
	Astrexp=exp(Index1,Index2,Std_exp,Std_exp_neg),
	append(Index1,Index2,Index_total),
	%add max/min
	get_maxs_mins(Max_min_set,bound(Op,Astrexp,Bounded),[],New_max_bounds),
	(New_max_bounds\=[]->
		append(New_max_bounds,Iconstrs,Iconstrs2),
		foldl(add_indexes_to_set,Index_total,Max_min_set,Max_min_set2)
	;
	  Iconstrs2=Iconstrs,
	  Max_min_set2=Max_min_set
	),
	
	% add sums
	get_mapped(Bounded,Sum_map,New_names),
	length(Bounded,N),
	(
	((Op=lb,length(New_names,N))
	;
	(Op=ub,New_names\=[])
	)
	->

	update_sum_map(Index1,Loop,Std_exp,Std_exp2,Index1_sum,Sum_map,Sum_map2),
	update_sum_map(Index2,Loop,Std_exp_neg,Std_exp_neg2,Index2_sum,Sum_map2,Sum_map3),
	%this means some are multiplied (the new names can be the same as the old if they did not coicide
	update_max_set(Index1,Std_exp2,Index1_max,Max_min_set2,Max_min_set3),
	update_max_set(Index2,Std_exp_neg2,Index2_max,Max_min_set3,Max_min_set4),
	

	append(Index1_max,Index1_sum,Index1_final),
	
	append(Index2_max,Index2_sum,Index2_final),
	Iconstrs3=[bound(Op,exp(Index1_final,Index2_final,Std_exp2,Std_exp_neg2),New_names)|Iconstrs2]
	;
	Iconstrs3=Iconstrs2,
	Sum_map3=Sum_map,
	Max_min_set4=Max_min_set2
	).
	



get_mapped([],_,[]).
get_mapped([X|Xs],Map,[New_name|New_names]):-
	lookup_lm(Map,X,New_name),!,
	get_mapped(Xs,Map,New_names).
get_mapped([_|Xs],Map,New_names):-
	get_mapped(Xs,Map,New_names).
	
add_indexes_to_set((Name,_Var),Max_map,Max_map2):-
	insert_sl(Max_map,Name,Max_map2).

update_sum_map(Index,Loop,Expr,Expr2,Index_final,Sum_map,Sum_map2):-
	get_first_factor(Expr,Expr2,Vars_set),
	include(pair_contains(Vars_set),Index,Index_sum),
	foldl(get_missing,Index,Vars_set,Missing),
	get_loop_itvar(Loop,Itvar),
	maplist(tuple(Itvar),Missing,Index_extra),
	substitute_by_new_name(Index_sum,Loop,Sum_map,Index_sum_substituted,Sum_map2),
	append(Index_extra,Index_sum_substituted,Index_final).

get_missing((_Name,Var),Set,Set1):-
	remove_sl(Set,Var,Set1).
	
substitute_by_new_name([],_,Sum_map,[],Sum_map).
substitute_by_new_name([(Name,Var)|Index_sum],Loop,Sum_map,[(New_name,Var)|Index_sum_substituted],Sum_map3):-
%	contains_sl(Max_map,Name),!,
	(lookup_lm(Sum_map,Name,New_name),Sum_map2=Sum_map
	;
	itvar_extend_name(sum(Loop),Name,New_name),
%	new_itvar(New_name),
	insert_lm(Sum_map,Name,New_name,Sum_map2)),
	substitute_by_new_name(Index_sum,Loop,Sum_map2,Index_sum_substituted,Sum_map3).
	
update_max_set(Index,Expr,Index_max,Max_set,Max_set2):-
	get_all_but_first_factor(Expr,Vars_set),
	include(pair_contains(Vars_set),Index,Index_max),
	maplist(tuple,Names,_,Index_max),
	from_list_sl(Names,Names_set),
	union_sl(Names_set,Max_set,Max_set2).

pair_contains_first(Set,(F,_)):-
	contains_sl(Set,F).	
pair_contains(Set,(_,Var)):-
	contains_sl(Set,Var).
	
get_all_but_first_factor(add(Summands),Vars):-
	maplist(get_all_but_first_factor_1,Summands,Vars_list),
	unions_sl(Vars_list,Vars).
get_all_but_first_factor_1(mult(Factors),Vars_set1):-
	member(First_factor,Factors),
	var(First_factor),!,
	term_variables(Factors,Vars),
	from_list_sl(Vars,Vars_set),
	remove_sl(Vars_set,First_factor,Vars_set1).
	
get_first_factor(add(Summands),add(Summands1),Vars):-	
	maplist(get_first_factor_1,Summands,Summands1,Vars_list),
	unions_sl(Vars_list,Vars).
get_first_factor_1(mult(Factors),mult(Factors),[First_valid]):-
	member(First_valid,Factors),
	var(First_valid),!.
get_first_factor_1(mult(Factors),mult([Itvar|Factors]),[Itvar]).


	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	



%! cstr_or_compress(Costs:list(cstr),Cost_final:cstr) is det
%  given a list of cost structures, generate a cost structure that represents the disjunction of all 
%  cost structures. 
cstr_or_compress([Cost],Cost):-!.

%if we are not computing lower bounds (or cost with negative annotations),
% we overapproximate the final cost to the sum of all the possible costs
cstr_or_compress(Costs,Cost_final):-
	\+get_param(compute_lbs,[]),!,
	from_list_sl(Costs,Costs_set),
	cstr_get_components(Costs_set,Ub_fcons_list,_,Itcons_list,BSummands_list,BConstants),
	ut_flat_list(Ub_fcons_list,Ub_fcons_flat),
	ut_flat_list(Itcons_list,Itcons_flat),
	ut_flat_list(BSummands_list,BSummands_flat),
	max_frl(BConstants,BConstant),
	(maplist(is_constant_bconstr,Ub_fcons_flat)->
	    cstr_maxminimization(cost(Ub_fcons_flat,[],Itcons_flat,BSummands_flat,BConstant),max,none,[],New_BConstant),
	    strexp_simplify_max_min(New_BConstant,Cost_max_min_simple),
		strexp_to_cost_expression(Cost_max_min_simple,New_BConstant_cexpr),
	    cexpr_simplify(New_BConstant_cexpr,[],New_BConstant_simpl),
	    (is_rational(New_BConstant_simpl)->
	        cstr_from_cexpr(New_BConstant_simpl,Cost_final)
	        ;
	        cstr_infinite(Cost_final)
	        )
	;
	 cstr_simplify(cost(Ub_fcons_flat,[],Itcons_flat,BSummands_flat,BConstant),Cost_final)
	 ).

%FIXME 
% creates inefficient structures
% when the cost is a constant, the auxiliary expressions are not well propagated	 
cstr_or_compress(Costs,Cost_final):-
	%remove duplicates
	from_list_sl(Costs,Costs_set),
	cstr_get_components(Costs_set,Ub_fcons_list,Lb_fcons_list,Itcons_list,BSummands_list,BConstants),
	maplist(get_bconstrs_from_bsummands,BSummands_list,BConstants,Pos_extra,Neg_extra),
	ut_flat_list(Pos_extra,Pos_extra_flat),
	ut_flat_list(Neg_extra,Neg_extra_flat),
	maplist(tuple,Pos_extra_ub,Pos_extra_lb,Pos_extra_flat),
	maplist(tuple,Neg_extra_ub,Neg_extra_lb,Neg_extra_flat),
	maplist(bconstr_get_bounded,Pos_extra_ub,Bounded_pos),
	maplist(bconstr_get_bounded,Neg_extra_ub,Bounded_neg),
	foldl(append,Bounded_pos,[],Bounded_pos_flat),
	foldl(append,Bounded_neg,[],Bounded_neg_flat),
	get_disjunction_aux(Bounded_pos_flat,Pos_disjunct_auxs,Pos_disjunct_fconstrs),
	get_disjunction_aux(Bounded_neg_flat,Neg_disjunct_auxs,Neg_disjunct_fconstrs),
	(Pos_disjunct_auxs=[bound(_,_,[Bounded_pos_final])|_]->
	    BSummands=[(Bounded_pos_final,1)]
	    ;
	    BSummands=[]
	 ),
	(Neg_disjunct_auxs=[bound(_,_,[Bounded_neg_final])|_]->
		BSummands1=[(Bounded_neg_final,1)|BSummands]
	    ;
	    BSummands1=BSummands
	),
	ut_flat_list([Pos_extra_ub,Pos_extra_lb,Neg_extra_ub,Neg_extra_lb],Extra_total),
	partition(is_inter_bconstr,Extra_total,Iconstrs_extra,Top_extra),
	ut_flat_list([Top_extra,Pos_disjunct_fconstrs,Ub_fcons_list,Neg_disjunct_fconstrs,Lb_fcons_list],Fcons_all),
	partition(is_ub_bconstr,Fcons_all,Ub_fcons,Lb_fcons),
	ut_flat_list([Itcons_list,Iconstrs_extra,Pos_disjunct_auxs,Neg_disjunct_auxs],Iconstrs),
	cstr_simplify(cost(Ub_fcons,Lb_fcons,Iconstrs,BSummands1,0),Cost_final).


get_disjunction_aux([],[],[]):-!.

get_disjunction_aux(Vars,[Ub_disjunct_aux,Lb_disjunct_aux],[Ub_disjunct_fconstr,Lb_disjunct_fconstr]):-
	get_summand_multiplied(Vars,Index_pos,Summands,New_vars),
	Internal_exp=exp(Index_pos,[],add(Summands),add([])),
	copy_term(Internal_exp,Internal_exp2),
	new_itvar(Aux_var),
	Ub_disjunct_aux=bound(ub,Internal_exp,[Aux_var]),
	Lb_disjunct_aux=bound(lb,Internal_exp2,[Aux_var]),
	Ub_disjunct_fconstr=bound(ub,[]+1,New_vars),
	Lb_disjunct_fconstr=bound(lb,[]+1,New_vars).

get_summand_multiplied([],[],[],[]).
get_summand_multiplied([Name|Names],[(Name,Var1),(Name_new,Var2)|Index_rest],[mult([Var1,Var2])|Summands],[Name_new|Names_new]):-
	new_itvar(Name_new),
	get_summand_multiplied(Names,Index_rest,Summands,Names_new).


get_bconstrs_from_bsummands([],BConstant,Pos_aux,Neg_aux):-!,
	(greater_fr(BConstant,0)->
	    new_itvar(Aux_var_pos),
	    Pos_aux=(bound(ub,[]+BConstant,[Aux_var_pos]),
	             bound(lb,[]+BConstant,[Aux_var_pos])),
	     Neg_aux=[]

	 ;
	  negate_fr(BConstant,BConstant_neg),
	  new_itvar(Aux_var_pos),
	    Neg_aux=(bound(ub,[]+BConstant_neg,[Aux_var_pos]),
	             bound(lb,[]+BConstant_neg,[Aux_var_pos])),
	     Pos_aux=[]
	  
	).

get_bconstrs_from_bsummands(BSummands,BConstant,Pos_aux,Neg_aux):-
	generate_summands_from_bsummands(BSummands,Index_pos,Index_neg,Summands_pos,Summands_neg),
	(greater_fr(BConstant,0)->
	    Summands_pos1=[mult([BConstant])|Summands_pos],
	    Summands_neg1=Summands_neg
	 ;
	  	negate_fr(BConstant,BConstant_neg),
	  	Summands_pos1=Summands_pos,
	    Summands_neg1=[mult([BConstant_neg])|Summands_neg]
	),
	(Summands_pos1\=[]->
	new_itvar(Aux_var_pos),
	   Pos_aux=(bound(ub,exp(Index_pos,[],add(Summands_pos1),add([])),[Aux_var_pos]),
	   	        bound(lb,exp(Index_pos,[],add(Summands_pos1),add([])),[Aux_var_pos]))
	   ;
	   Pos_aux=[]
	   ),
	(Summands_neg1\=[]->
	new_itvar(Aux_var_neg),
	   Neg_aux=(bound(ub,exp(Index_neg,[],add(Summands_neg1),add([])),[Aux_var_neg]),
	            bound(lb,exp(Index_neg,[],add(Summands_neg1),add([])),[Aux_var_neg]))
	   ;
	   Neg_aux=[]
	   ).
	
generate_summands_from_bsummands([],[],[],[],[]).
generate_summands_from_bsummands([(Name,1)|BConstants],[(Name,Var)|Index_pos],Index_neg,[mult([Var])|Summands_pos],Summands_neg):-!,
	generate_summands_from_bsummands(BConstants,Index_pos,Index_neg,Summands_pos,Summands_neg).
	
generate_summands_from_bsummands([(Name,Coeff)|BConstants],[(Name,Var)|Index_pos],Index_neg,[mult([Var,Coeff])|Summands_pos],Summands_neg):-
	geq_fr(Coeff,0),!,
	generate_summands_from_bsummands(BConstants,Index_pos,Index_neg,Summands_pos,Summands_neg).
generate_summands_from_bsummands([(Name,Coeff)|BConstants],Index_pos,[(Name,Var)|Index_neg],Summands_pos,[mult([Var,Coeff_neg])|Summands_neg]):-
	negate_fr(Coeff,Coeff_neg),
	generate_summands_from_bsummands(BConstants,Index_pos,Index_neg,Summands_pos,Summands_neg).	
	