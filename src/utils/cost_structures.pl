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
       * Bounded: list(itvar)
       * In a final constraint, Exp is a normalized linear expression (nlin_exp)
       * In an intermediate constraint, Exp is an abstract structured cost (astrexp)
     A constraint bound(op,Exp,Bounded) represents:
       *  sum(Bounded) =< Exp  if Op=ub
       *  sum(Bounded) >= Exp  if Op=lb
         
     
     Ub_FCons contains the final constraints with Op=ub
     Lb_FCons contains the final constraints with Op=lb
     Iconstrs contains all the intermediate constraints
     
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
		get_loop_depth_itvar/2,
		is_ub_bconstr/1,
		fconstr_new/4,
		fconstr_new_inv/4,
		iconstr_new/4,
		bconstr_get_bounded/2,
		bconstr_annotate_bounded/2,
		astrexp_new/2,
		pstrexp_pair_add/3,
		pstrexp_pair_empty/1,
		cstr_empty/1,
		astrexp_to_cexpr/2,
		basic_cost_to_astrexp/4,
		cstr_from_cexpr/2,
		cstr_remove_cycles/2,
		cstr_get_unbounded_itvars/2,
		cstr_extend_variables_names/3,
		itvar_recover_long_name/2,
		cstr_propagate_sums/4,
		cstr_join/3,
		cstr_or_compress/2,
		cstr_join_equal_fconstr/2,
		cstr_simplify/5,
		cstr_shorten_variables_names/3]).
		
		
:- use_module(cofloco_utils,[zip_with_op/3,is_rational/1,sort_with/3,write_sum/2,write_product/2,tuple/3,get_all_pairs/3,normalize_constraint/2]).
:- use_module(structured_cost_expression,[strexp_simplify_max_min/2,strexp_to_cost_expression/2]).	
:- use_module(cost_expressions,[cexpr_simplify/3,is_linear_exp/1]).	
:- use_module(polyhedra_optimizations,[nad_entails_aux/3]).	
:- use_module('../IO/params',[get_param/2]).
:- use_module('../IO/output',[print_aux_exp/1]).	
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
:- use_module(stdlib(counters),[counter_increase/3]).	
:- use_module(stdlib(utils),[ut_flat_list/2]).	
:- use_module(stdlib(multimap),[put_mm/4,from_pair_list_mm/2,values_of_mm/3]).	
:- use_module(stdlib(list_map),[lookup_lm/3,delete_lm/3,insert_lm/4]).

:- use_module(stdlib(fraction)).
:- use_module(stdlib(fraction_list)).
:- use_module(stdlib(set_list),[difference_sl/3,remove_sl/3,contains_sl/2,from_list_sl/2,unions_sl/2,union_sl/3,insert_sl/3,intersection_sl/3]).

:-dynamic short_db/3.
:-use_module(library(apply_macros)).
:-use_module(library(lists)).
:-use_module(library(terms)).




opposite_ub_lb(ub,lb).
opposite_ub_lb(lb,ub).

max_min_ub_lb(max,ub).
max_min_ub_lb(min,lb).

%predicates for intermediate variables
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%! new_itvar(Itvar:itvar) is det
% generate a fresh intermediate variable name
new_itvar([aux(Num)]):-
	counter_increase(aux_vars,1,Num).
	
%! get_loop_itvar(Loop:loop_id,Itvar:itvar) is det
% get the itvar corresponding to a loop identifier
get_loop_itvar(Loop,[it(Loop)]).

%! get_loop_depth_itvar(Loop:loop_id,Itvar:itvar) is det
% get the itvar corresponding to the depth of a loop identifier
get_loop_depth_itvar(Loop,[it_depth(Loop)]).

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
bconstr_accum_bounded_set(bound(_,_,Bounded),Set,Set1):-
	from_list_sl(Bounded,Bounded_set),
	union_sl(Bounded_set,Set,Set1).

%! fconstr_new(Bounded:list(itvar),Op:op,NLin_exp:nlin_exp,Fconstr:fconstr) is det
% create a new final constraint
fconstr_new(Bounded,Op,NLin_exp,bound(Op,NLin_exp,Bounded)).
fconstr_new_inv(NLin_exp,Op,Bounded,bound(Op,NLin_exp,Bounded)).

%! iconstr_new(Astrexp:astrexp,Bounded:list(itvar),Op:op,Iconstr:iconstr) is det
% create a new intermediate constraint
iconstr_new(Astrexp,Op,Bounded,bound(Op,Astrexp,Bounded)).


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
bconstr_remove_bounded(Set,bound(Op,Exp,Bounded),bound(Op,Exp,Bounded_set1)):-
	from_list_sl(Bounded,Bounded_set),
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

%! cstr_simplify(+Cstr:cstr,+Vars:list(var),+Phi:polyhedron,+Max_min:flag,-Cstr_simple:cstr)
% simplify the cost structure Cstr taking Phi into account
% Max_min_both can be 'max','min' or 'both' and indicates whether we want to obtain a maximum cost, minimum or both
cstr_simplify(Cstr,Vars,Phi,Max_min_both,Cstr_simple):-
	cstr_join_equal_fconstr(Cstr,Cstr1),
	cstr_simplify_fconstr_nats(Cstr1,Vars,Phi,Cstr2),
	cstr_propagate_zeroes(Cstr2,Cstr3),
	cstr_remove_useless_constrs(Cstr3,Max_min_both,Cstr4),
	Cstr4=Cstr_simple.

	
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


%! cstr_get_components(+Costs:list(cstr),-Ub_fcons:list(list(fconstr)),-Lb_fcons:list(list(fconstr)),-Itcons:list(list(iconstr)),-BSummands:list(list(bsummands)),-BConstants:list(constant)) is det
% obtain lists of the components of a cost structure separated
cstr_get_components([],[],[],[],[],[]).
cstr_get_components([cost(Ub_fcons,Lb_fcons,Itcons,BSummands,BConstant)|Rest],[Ub_fcons|Ub_fcons_rest],[Lb_fcons|Lb_fcons_rest],[Itcons|Itcons_rest],[BSummands|BSummands_res],[BConstant|BConstant_rest]):-
	cstr_get_components(Rest,Ub_fcons_rest,Lb_fcons_rest,Itcons_rest,BSummands_res,BConstant_rest).
	
	


%! cstr_join_equal_fconstr(+Cost:cstr,-Cost_simple:cstr) is det
% join all the final bound constraints that have the same linear expression
% and simplify intermediate constraints. Join intermediate variables that are subject to the same constraints
cstr_join_equal_fconstr(cost(Ub_fcons,Lb_fcons,Itcons,Bsummands,BConstant),Cost_final2):-
	%cstr_shorten_variables_names(Cost,list,cost(Ub_fcons,Lb_fcons,Itcons,Bsummands,BConstant)),
	fconstr_join_equal_expressions(Ub_fcons,Ub_fcons2,Extra_itcons1),
	fconstr_join_equal_expressions(Lb_fcons,Lb_fcons2,Extra_itcons2),
	ut_flat_list([Extra_itcons1,Extra_itcons2,Itcons],Itcons2),
	join_equivalent_itvars(cost(Ub_fcons2,Lb_fcons2,Itcons2,Bsummands,BConstant),Cost_final),
	cstr_remove_cycles(Cost_final,Cost_final2).



join_equivalent_itvars(cost(Ub_fcons,Lb_fcons,Itcons,Bsummands,BConstant),cost(Ub_fcons,Lb_fcons,Itcons3,Bsummands3,BConstant)):-
	partition(bconstr_bounds_multiple_itvars,Itcons,Multiple_itconstrs,Single_itconstrs),
	%TODO: the unbounded variables that appear adding and substracting should not be joined!! 
	% join the positive together and the negative together but do not mix them
	foldl(add_itvar_empty_map,Bsummands,[],Map_0),
	%Map_0=[],
	foldl(get_itconstr_for_each_itvar,Single_itconstrs,Map_0,Map),
	foldl(remove_itvars_from_map,Ub_fcons,Map,Map1),
	foldl(remove_itvars_from_map,Lb_fcons,Map1,Map2),
	foldl(remove_itvars_from_map,Multiple_itconstrs,Map2,Map3),
	maplist(tuple,Itvar,Itconstr_set,Map3),
	maplist(tuple,Itconstr_set,Itvar,Map_inv),
	from_pair_list_mm(Map_inv,Multimap),
	maplist(tuple,_,Itvar_sets,Multimap),
	include(is_multiple_set,Itvar_sets,Itvar_multiple_sets),	
	(Itvar_multiple_sets\=[]->
		foldl(join_itvar_set,Itvar_multiple_sets,(Itcons,Bsummands),(Itcons2,Bsummands2)),
		join_equivalent_itvars(cost(Ub_fcons,Lb_fcons,Itcons2,Bsummands2,BConstant),cost(Ub_fcons,Lb_fcons,Itcons3,Bsummands3,BConstant))
		;
		Itcons3=Itcons,
		Bsummands3=Bsummands
	).


add_itvar_empty_map((Itvar,Coeff),Map,Map1):-
	Coeff>0,!,
	insert_lm(Map,Itvar,[pos],Map1).
add_itvar_empty_map((Itvar,_),Map,Map1):-
	insert_lm(Map,Itvar,[neg],Map1).	
	
	
get_itconstr_for_each_itvar(bound(Op,Exp,[Itvar]),Map,Map1):-!,
	copy_term(Exp,Exp2),
	Exp2=exp(Index_pos,Index_neg,_,_),
	maplist(ground_index,Index_pos),
	maplist(ground_index,Index_neg),
	term_hash((Op,Exp2),Hash),
	put_mm(Map,Itvar,Hash,Map1).


	
remove_itvars_from_map(bound(_,_,Bounded),Map,Map1):-
	foldl(delete_lm_aux,Bounded,Map,Map1).
	
delete_lm_aux(Key,Map,Map1):-
	delete_lm(Map,Key,Map1).
	
is_multiple_set([_,_|_]).	

join_itvar_set([Itvar|Equivalent_itvars],(Itconstrs,Bsummands),(Itconstrs4,Bsummands2)):-
	from_list_sl(Equivalent_itvars,Equivalent_itvars_set),
	exclude(bconstr_bounds_itvars(Equivalent_itvars_set),Itconstrs,Itconstrs2),
	foldl(itconstr_substitute_itvars_in_exp(Itvar,Equivalent_itvars_set),Itconstrs2,([],[]),(_,Itconstrs3)),
	reverse(Itconstrs3,Itconstrs4),
	foldl(compress_basic_summands(Itvar,Equivalent_itvars_set),Bsummands,[],Bsummands2).

bconstr_bounds_itvars(Set,bound(_,_,Bounded)):-
	from_list_sl(Bounded,Bounded_set),
	intersection_sl(Set,Bounded_set,[_|_]).

itconstr_substitute_itvars_in_exp(Itvar,Equiv_itvar_set,bound(Op,Exp,Bounded),(Bconstrs_hash_set,Bconstrs),Pair1):-
	Exp=exp(Index_pos,Index_neg,Pos,Neg),
	maplist(substitute_itvars_in_index(Itvar,Equiv_itvar_set),Index_pos,Index_pos2),
	maplist(substitute_itvars_in_index(Itvar,Equiv_itvar_set),Index_neg,Index_neg2),
	Exp2=exp(Index_pos2,Index_neg2,Pos,Neg),
	copy_term(Exp2,Exp_ground),
	Exp_ground=exp(Index_pos_ground,Index_neg_ground,_,_),
	
	maplist(ground_index,Index_pos_ground),
	maplist(ground_index,Index_neg_ground),
	term_hash(bound(Op,Exp_ground,Bounded),Hash_new_bconstr),
	(contains_sl(Bconstrs_hash_set,Hash_new_bconstr)->
		Pair1=(Bconstrs_hash_set,Bconstrs)
		;
		insert_sl(Bconstrs_hash_set,Hash_new_bconstr,Bconstrs_hash_set1),
		Bconstrs1=[bound(Op,Exp2,Bounded)|Bconstrs],
		Pair1=(Bconstrs_hash_set1,Bconstrs1)
	).

substitute_itvars_in_index(Itvar,Equiv_itvar_set,(Itvar2,Var),(Itvar,Var)):-
	contains_sl(Equiv_itvar_set,Itvar2),!.
substitute_itvars_in_index(_Itvar,_Equiv_itvar_set,(Itvar2,Var),(Itvar2,Var)).

compress_basic_summands(Itvar,Equiv_itvars_set,(Itvar2,Coeff),Map,Map1):-
	contains_sl(Equiv_itvars_set,Itvar2),!,
	accum_basic_summand(Itvar,Coeff,Map,Map1).
	
compress_basic_summands(_Itvar,_Equiv_itvars_set,(Itvar2,Coeff),Map,Map1):-
	accum_basic_summand(Itvar2,Coeff,Map,Map1).	

accum_basic_summand(Itvar,Coeff,Map,Map1):-
	(lookup_lm(Map,Itvar,Coeff2)->
		sum_fr(Coeff,Coeff2,Coeff3),
		insert_lm(Map,Itvar,Coeff3,Map1)
	;
		insert_lm(Map,Itvar,Coeff,Map1)
	).
	
ground_index((X,X)):-!.
ground_index(_).
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
	astrexp_new_simple_itvar(Name,Astrexp),
	maplist(iconstr_new(Astrexp,Op),Bounded_list,New_iconstrs).
	

	
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
propagate_zeroes_through_iconstrs([bound(Op,Exp,Bounded)|Iconstrs],Set,Iconstrs_out,Set_out):-
	Exp=exp(Index_pos,Index_neg,Pos,Neg),
	partition(pair_contains_first(Set),Index_pos,Index_zero,Index_pos1),
	Index_zero\=[],!,
	maplist(set_second_to(0),Index_zero),
	simplify_add(Pos,Pos1),
	(Pos1=add([])->
	   Iconstrs_out=Iconstrs_out1,
	   from_list_sl(Bounded,Bounded_set),
	   union_sl(Bounded_set,Set,Set1)
	   ;
	   Exp1=exp(Index_pos1,Index_neg,Pos1,Neg),
	   bconstr_remove_bounded(Set,bound(Op,Exp1,Bounded),Iconstr),
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

%! cstr_remove_cycles(+Cost:cstr,-Short:cstr) is det
% one of the main simplifying predicates for cost structures
% remove constraints that depend on variables that are not bounded anywhere
% get rid of circular dependencies	


cstr_remove_cycles(cost(Ub_fconstrs,Lb_fconstrs,Iconstrs,Bsummands,BConstant),Short):-
	foldl(bconstr_accum_bounded_set,Ub_fconstrs,[],Ub_Bounded_set),
	foldl(bconstr_accum_bounded_set,Lb_fconstrs,[],Lb_Bounded_set),
%	find_cycles(Iconstrs,Iconstrs1),!,
%	find_cycles(Iconstrs1,Iconstrs11),!,
%	find_cycles(Iconstrs11,Iconstrs2),!,
	Iconstrs=Iconstrs2,
	remove_not_bounded(Iconstrs2,Ub_Bounded_set,Lb_Bounded_set,Iconstrs3),
	%Some other simplifications
	cstr_propagate_zeroes(cost(Ub_fconstrs,Lb_fconstrs,Iconstrs3,Bsummands,BConstant),Simplified1),
	cstr_remove_useless_constrs(Simplified1,both,Simplified),
	cstr_shorten_variables_names(Simplified,list,Short).

:- use_module(stdlib(scc),[compute_sccs/2]).

find_cycles(Iconstrs,Iconstrs2):-
	foldl(iconstr_create_edges,Iconstrs,[],Graph),
	compute_sccs(Graph,SCCs),
	include(is_recursive_scc,SCCs,Recursive),
	foldl(solve_cycle,Recursive,Iconstrs,Iconstrs2).

solve_cycle((recursive,Itvars),Iconstrs,Iconstrs2):-
	from_list_sl(Itvars,Itvars_set),
	partition(involved_iconstr(Itvars_set),Iconstrs,Involved,Innocent),
	(
	solve_cycle_1(Itvars_set,Involved,New_constrs)
	;
	New_constrs=Involved
	),
	append(New_constrs,Innocent,Iconstrs2).




involved_iconstr(Itvars_set,bound(_,exp(Index_pos,Index_neg,_,_),Bounded)):-
	from_list_sl(Bounded,Bounded_set),
	intersection_sl(Itvars_set,Bounded_set,[_|_]),
	(
	member((Itvar,_),Index_pos),
	contains_sl(Itvars_set,Itvar)
	;
	member((Itvar,_),Index_neg),
	contains_sl(Itvars_set,Itvar)
	),!.

solve_cycle_1(Itvars_set,Iconstrs,[Extra_iconstr|Iconstrs2]):-
	maplist(writeln,Iconstrs),
	foldl(get_positive_linear_constraint(Itvars_set),Iconstrs,([],[]),(Map,Linear_constrs)),
	term_variables(Map,Vars),
	maplist(lookup_lm(Map),Itvars_set,Bad_vars),
	from_list_sl(Bad_vars,Bad_vars_set),
	from_list_sl(Vars,Vars_set),

	%(Name=[it(18)];true),
	%trace,
	%(member([it(Loop)],Itvars_set),Name=[it(Loop)]
	%;
	member(Name,Itvars_set)
	%)
	,
	lookup_lm(Map,Name,Var),
	difference_sl(Vars_set,Bad_vars_set,Vars_of_interest),
	max_min_linear_expression_all([(Var,1)]+0, Vars_of_interest, Linear_constrs,max, Lin_exp_out),
	Lin_exp_out=[BSummands+BConstant|_],!,
	writeln(solved),
	maplist(unify_pair,Map),
	foldl(get_summands_aux,BSummands,[mult([BConstant])],Summands),
	astrexp_new(add(Summands)-add([]),Exp),
	%Iconstrs=Iconstrs2,
	exclude(contains_bounded_var(Var),Iconstrs,Iconstrs2),
	Extra_iconstr=bound(ub,Exp,[Var]).
	
get_summands_aux((X,1),Summands,[mult([X])|Summands]):-!.
get_summands_aux((X,Coeff),Summands,[mult([X,Coeff])|Summands]).
	
	
contains_bounded_var(Var,bound(_,_,[Bounded])):-
	Var=Bounded.

%it asumes that cycles and undefined constraints have been removed 
cstr_get_unbounded_itvars(cost(Top_exps,_LTop_exps,Aux_exps,Bases,_Base),Unbounded):-
	foldl(get_bounded_itvars(ub),Top_exps,[],Bounded_aux),
	foldl(get_bounded_itvars(ub),Aux_exps,Bounded_aux,Bounded),
	maplist(tuple,Itvars,_,Bases),
	from_list_sl(Itvars,Itvars_set),
	difference_sl(Itvars_set,Bounded,Unbounded).
get_bounded_itvars(Op,bound(Op,_,Bounded),Bounded_set,Bounded_set1):-!,
	from_list_sl(Bounded,Bounded_set_new),
	union_sl(Bounded_set,Bounded_set_new,Bounded_set1).
get_bounded_itvars(_,_,Bounded_set,Bounded_set).


get_positive_linear_constraint(_Itvars_set,bound(Op,exp(Index_pos,[],add(Summands),add([])),Bounded),(Map,Lin_exps),(Map2,[Lin_exp_norm|Lin_exps])):-
	copy_term((Index_pos,Summands),(Index_pos_c,Summands_c)),
	maplist(unify_pair,Index_pos_c),
	foldl(get_left_side,Summands_c,(Map,[]),(Map1,Summands_left)),
	write_sum(Summands_left,Left),
	foldl(translate,Bounded,(Map1,[]),(Map2,List_vars)),
	write_sum(List_vars,Right),
	get_rel_op(Op,Rel_op),
	Lin_exp=..[Rel_op,Left,Right],
	normalize_constraint(Lin_exp,Lin_exp_norm),!.
	
get_positive_linear_constraint(_Itvars_set,_,(Map,Lin_exps),(Map,Lin_exps)).


get_left_side(mult(Factors),(Map,Summands),(Map1,[Summand|Summands])):-
	partition(is_rational,Factors,Coeffs,Vars),
	product_frl([1|Coeffs],Coeff),
	(Vars=[]->
		Summand=Coeff,
		Map1=Map
	;
	Vars=[Var],
	Var\=max(_),Var\=min(_),
	translate(Var,(Map,[]),(Map1,[Var2])),
	Summand=Coeff*Var2
	).

translate(Name,(Map,Vars),(Map,[Var|Vars])):-
	lookup_lm(Map,Name,Var),!.
translate(Name,(Map,Vars),(Map1,[Var|Vars])):-
	insert_lm(Map,Name,Var,Map1),!.	
	
get_rel_op(ub,'>=').
get_rel_op(lb,'=<').

unify_pair((X,X)).
is_recursive_scc((recursive,_)).

iconstr_create_edges(bound(ub,exp(Index_pos,_Index_neg,_,_),Bounded),Edges_accum,Edges):-
	maplist(tuple,Target_vars1,_,Index_pos),
	%maplist(tuple,Target_vars2,_,Index_neg),
	foldl(get_all_combinations(Target_vars1),Bounded,Edges_accum,Edges).
	
iconstr_create_edges(bound(lb,exp(_Index_pos,Index_neg,_,_),Bounded),Edges_accum,Edges):-
	%maplist(tuple,Target_vars1,_,Index_pos),
	maplist(tuple,Target_vars2,_,Index_neg),
	foldl(get_all_combinations(Target_vars2),Bounded,Edges_accum,Edges).

get_all_combinations(Xs,Y,Edges_accum,Edges):-
	foldl(get_all_combinations1(Y),Xs,Edges_accum,Edges).

get_all_combinations1(Y,X,Edges,[Y-X|Edges]).

%! remove_not_bounded(Iconstrs:list(iconstrs),Ub_Set:list_set(itvar),Lb_Set:list_set(itvar),Iconstrs_out:list(iconstrs)) is det
%  in each iteration accumulate the iconstrs that are well defined (all the itvars in their expressions are bounded)
%  also accumulate the itvars that become well defined by the selected iconstrs
%  keep iterating until no more iconstrs can be included (a fixpoint has been reached)
remove_not_bounded(Iconstrs,Ub_Set,Lb_Set,Iconstrs_out):-
	split_bounded(Iconstrs,Ub_Set,Lb_Set,Ub_Set_1,Lb_Set_1,Bounded,Not_bounded),
	(Bounded=[]->
	  Iconstrs_out=[]
	  %,(Not_bounded\=[]->trace,maplist(print_aux_exp,Not_bounded);true)
	;
	  remove_not_bounded(Not_bounded,Ub_Set_1,Lb_Set_1,Iconstrs_aux),
	  append(Bounded,Iconstrs_aux,Iconstrs_out)
	  ).
	  
split_bounded([],Ub_Set,Lb_Set,Ub_Set,Lb_Set,[],[]).

split_bounded([bound(ub,exp(Index,Index_neg,Exp,Exp_neg),Bounded)|Iconstrs],Ub_Set,Lb_Set,Ub_Set_out,Lb_Set_out,[bound(ub,exp(Index,Index_neg,Exp,Exp_neg),Bounded)|Exp_Bounded],Exp_Not_bounded):-
	% the positive summands have to be well defined
	maplist(tuple,Names,_Vars,Index),
	maplist(contains_sl(Ub_Set),Names),!,
	%include Bounded into the Ub_set
	from_list_sl(Bounded,Bounded_set),
	union_sl(Bounded_set,Ub_Set,Ub_Set_aux),
	split_bounded(Iconstrs,Ub_Set_aux,Lb_Set,Ub_Set_out,Lb_Set_out,Exp_Bounded,Exp_Not_bounded).

% FIXME: the positive summands do not need to be well defined in theory but it might help...make some experiments
split_bounded([bound(lb,exp(Index,Index_neg,Exp,Exp_neg),Bounded)|Iconstrs],Ub_Set,Lb_Set,Ub_Set_out,Lb_Set_out,[bound(lb,exp(Index,Index_neg,Exp,Exp_neg),Bounded)|Exp_Bounded],Exp_Not_bounded):-
	% the negative summands have to be well defined
	maplist(tuple,Names,_,Index),
	maplist(contains_sl(Lb_Set),Names),
	maplist(tuple,Names_neg,_,Index_neg),
	maplist(contains_sl(Ub_Set),Names_neg),!,
	%include Bounded into the Lb_set
	from_list_sl(Bounded,Bounded_set),
	union_sl(Bounded_set,Lb_Set,Lb_Set_aux),
	split_bounded(Iconstrs,Ub_Set,Lb_Set_aux,Ub_Set_out,Lb_Set_out,Exp_Bounded,Exp_Not_bounded).	
	
% Iconstr is not well defined
split_bounded([Iconstr|Iconstrs],Ub_Set,Lb_Set,Ub_Set_out,Lb_Set_out,Exp_Bounded,[Iconstr|Exp_Not_bounded]):-
	split_bounded(Iconstrs,Ub_Set,Lb_Set,Ub_Set_out,Lb_Set_out,Exp_Bounded,Exp_Not_bounded).



%! cstr_remove_useless_constrs(+Cost:cstr,-Cost_simple:cstr) is det
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
		maplist(bfactor_extend_name(Prefix),Bsummands,Bsummands1).



iconstr_extend_name(Prefix,bound(Op,Exp,Bounded),bound(Op,Exp1,Bounded2)):-
	astrexp_extend_name(Prefix,Exp,Exp1),
	maplist(append([Prefix]),Bounded,Bounded2).
	
fconstr_extend_name(Prefix,bound(Op,Expression,Bounded),bound(Op,Expression,Bounded2)):-
	maplist(append([Prefix]),Bounded,Bounded2).	
	
astrexp_extend_name(Prefix,exp(Index,Index_neg,Exp,Exp_neg),exp(Index2,Index_neg2,Exp,Exp_neg)):-
	maplist(bfactor_extend_name(Prefix),Index,Index2),
	maplist(bfactor_extend_name(Prefix),Index_neg,Index_neg2).	
	
bfactor_extend_name(Prefix,(Name,Value),([Prefix|Name],Value)).	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! cstr_shorten_variables_names(+Cost:cstr,+Flag:atom,-Cost_extended:cstr) is det
% Reduce the length of the itvar names by substituting them by their hash summary
% the flag indicates whether the resulting names are lists or terms
cstr_shorten_variables_names(cost(Ub_fconstrs,Lb_fconstrs,Iconstrs,Bsummands,BConstant),Flag,cost(Ub_fconstrs1,Lb_fconstrs1,Iconstrs1,Bsummands1,BConstant)):-
		maplist(fconstr_shorten_name(Flag),Ub_fconstrs,Ub_fconstrs1),
		maplist(fconstr_shorten_name(Flag),Lb_fconstrs,Lb_fconstrs1),
		maplist(iconstr_shorten_name(Flag),Iconstrs,Iconstrs1),
		maplist(bfactor_shorten_name(Flag),Bsummands,Bsummands1).
		

iconstr_shorten_name(Flag,bound(Op,Expression,Bounded),bound(Op,Expression2,Bounded2)):-
	astrexp_shorten_name(Flag,Expression,Expression2),
	maplist(itvar_shorten_name(Flag),Bounded,Bounded2).
	
fconstr_shorten_name(Flag,bound(Op,Expression,Bounded),bound(Op,Expression,Bounded2)):-
	maplist(itvar_shorten_name(Flag),Bounded,Bounded2).		

astrexp_shorten_name(Flag,exp(Index,Index_neg,Exp,Exp_neg),exp(Index2,Index_neg2,Exp,Exp_neg)):-
	maplist(bfactor_shorten_name(Flag),Index,Index2),
	maplist(bfactor_shorten_name(Flag),Index_neg,Index_neg2).
	
bfactor_shorten_name(Flag,(Name,Value),(Short_name,Value)):-
	itvar_shorten_name(Flag,Name,Short_name).	
	
%! itvar_shorten_name(+Flag:flag,+Itvar:itvar,-Itvar_short:itvar) is det
% create an abbreviation of the intermediate variable name
% the flag determines is the new name is a list or not. 
% The name must always be a list except when we want to use it for the output
itvar_shorten_name(list,Name,Short_name):-
	term_hash(Name,Hash),
	(short_db(Hash,Name,Short_name)->
		true
		;
	 	counter_increase(short_terms,1,Id),
	 	assert(short_db(Hash,Name,[s(Id)])),
	 	Short_name=[s(Id)]
	 	).
itvar_shorten_name(no_list,Name,Short_name):-
	term_hash(Name,Hash),
	(short_db(Hash,Name,Short_name)->
		true
		;
	 	counter_increase(short_terms,1,Id),
	 	assert(short_db(Hash,Name,s(Id))),
	 	Short_name=s(Id)
	 	).	

itvar_recover_long_name(Name,Long_name2):-
	short_db(_,Long_name1,Name),!,
	itvar_recover_long_name(Long_name1,Long_name2).

itvar_recover_long_name([Name],Long_name2):-
	short_db(_,Long_name1,Name),!,
	itvar_recover_long_name(Long_name1,Long_name2).		
itvar_recover_long_name([Name],[Name]):-!.

itvar_recover_long_name([Name1|Names],[Name1|Long_name]):-
	itvar_recover_long_name(Names,Long_name).


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
	foldl(generate_initial_sum_map,Bsummands,Bsummands1,[],Sum_map_initial),
	get_loop_itvar(Loop,Itvar),
	propagate_sums_backwards(Iconstrs,Itvar,Sum_map_initial,Iconstrs2,Sum_map,Max_min_set),
	Cost2=cost([],[],Iconstrs2,[(Itvar,BConstant)|Bsummands1],0),
	% get the final constraints that have to be computed
	foldl(get_maxs_mins(Max_min_set),Ub_fconstrs,[],Max_mins1),
	foldl(get_sums(Sum_map),Ub_fconstrs,[],Sums1),
	foldl(get_maxs_mins(Max_min_set),Lb_fconstrs,Max_mins1,Max_mins),
	foldl(get_sums(Sum_map),Lb_fconstrs,Sums1,Sums).



generate_initial_sum_map((Name,Val),(Name2,Val),Map,Map):-
	lookup_lm(Map,Name,Name2),!.
generate_initial_sum_map((Name,Val),(Name2,Val),Map,Map1):-
	new_itvar(Name2),
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


propagate_sums_backwards(Iconstrs,Itvar,Sum_map_initial,Iconstrs2,Sum_map,Max_min_set):-
	reverse(Iconstrs,Iconstrs_rev),
	foldl(propagate_sums(Itvar),Iconstrs_rev,([],[],Sum_map_initial),(Iconstrs2,Max_min_set,Sum_map)).

propagate_sums(Itvar,bound(Op,Astrexp,Bounded),(Iconstrs,Max_min_set,Sum_map),(Iconstrs3,Max_min_set4,Sum_map3)):-	
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

	update_sum_map(Index1,Itvar,Std_exp,Std_exp2,Index1_sum,Sum_map,Sum_map2),
	update_sum_map(Index2,Itvar,Std_exp_neg,Std_exp_neg2,Index2_sum,Sum_map2,Sum_map3),
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

update_sum_map(Index,Itvar,Expr,Expr2,Index_final,Sum_map,Sum_map2):-
	get_first_factor(Expr,Expr2,Vars_set),
	include(pair_contains(Vars_set),Index,Index_sum),
	foldl(get_missing,Index,Vars_set,Missing),
	maplist(tuple(Itvar),Missing,Index_extra),
	substitute_by_new_name(Index_sum,Sum_map,Index_sum_substituted,Sum_map2),
	append(Index_extra,Index_sum_substituted,Index_final).

get_missing((_Name,Var),Set,Set1):-
	remove_sl(Set,Var,Set1).
	
substitute_by_new_name([],Sum_map,[],Sum_map).
substitute_by_new_name([(Name,Var)|Index_sum],Sum_map,[(New_name,Var)|Index_sum_substituted],Sum_map3):-
%	contains_sl(Max_map,Name),!,
	(lookup_lm(Sum_map,Name,New_name),Sum_map2=Sum_map
	;
	new_itvar(New_name),
	insert_lm(Sum_map,Name,New_name,Sum_map2)),
	substitute_by_new_name(Index_sum,Sum_map2,Index_sum_substituted,Sum_map3).
	
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
	 cstr_join_equal_fconstr(cost(Ub_fcons_flat,[],Itcons_flat,BSummands_flat,BConstant),Cost_final)
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
	cstr_join_equal_fconstr(cost(Ub_fcons,Lb_fcons,Iconstrs,BSummands1,0),Cost_final).


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
	