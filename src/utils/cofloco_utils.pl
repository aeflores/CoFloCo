/** <module> cofloco_utils

This module implements general predicates that are used in different parts
of CoFloCo.

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


:- module(cofloco_utils,[
			zip_with_op/3,
		    zip_with_op2/4,
		    tuple/3,
		    sorted_tuple/3,
		    same_var_tuple/1,
		    is_rational/1,
		    normalize_constraint/2,
		    assign_right_vars/3,
		    constraint_to_coeffs_rep/2,
		    repeat_n_times/3,
		    bagof_no_fail/3,
		    foldr/4,
		    sort_with/3,
		    ground_copy/2,
		    write_sum/2,
		    write_le_internal/2,
		    write_product/2,
		    get_all_pairs/3,
		    normalize_constraint_wrt_var/3,
		    normalize_constraint_wrt_vars/3,
		    merge_implied_summaries/3]).


:- use_module(polyhedra_optimizations,[nad_entails_aux/3,nad_normalize_polyhedron/2]).
:- use_module(stdlib(set_list)).
:- use_module(stdlib(numeric_abstract_domains),[nad_project/3,nad_entails/3,nad_consistent_constraints/1,nad_lub/6,nad_list_lub/2]).
:- use_module(stdlib(linear_expression), [parse_le_fast/2,subtract_le/3,parse_le/2, integrate_le/3]).
:- use_module(stdlib(fraction),[divide_fr/3,negate_fr/2,geq_fr/2,gcd_fr/3]).
:- use_module(stdlib(polyhedra_ppl)).
:- use_module(stdlib(numvars_util),[to_numbervars_nu/4]).

:-use_module(library(apply_macros)).
:-use_module(library(lists)).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! merge_implied_summaries(+Vars:list(var),+Multimap:list(polyhedron,set_list(id)),+Compressed:list(polyhedron,set_list(id))) is det
% join the set_list(id) whose characteristic polyhedron is implied or implies the others
% keeping the most general polyhedron
merge_implied_summaries(Vars,Multimap,Compressed):-
	% we perform the comparisons with ppl polyhedra to gain efficiency
	maplist(generate_ppl_polyhedra_pairs(Vars),Multimap,Multimap_lowlevel),
	merge_implied_summaries_low_level(Multimap_lowlevel,Compressed_lowlevel),
	maplist(generate_contraints_pairs(Vars),Compressed_lowlevel,Compressed).
	
merge_implied_summaries_low_level([],[]).
merge_implied_summaries_low_level([(Inv,Ids)|Multimap],[Compressed_pair|Compressed]):-
	merge_implied_summaries_aux(Multimap,(Inv,Ids),Compressed_pair,Rest),
	merge_implied_summaries_low_level(Rest,Compressed).
	
merge_implied_summaries_aux([],(Inv,Ids),(Inv,Ids),[]).
merge_implied_summaries_aux([(Inv2,Ids2)|Multimap],(Inv,Ids),Compressed_pair,Rest):-
	ppl_Polyhedron_contains_Polyhedron(Inv2,Inv),!,
	ppl_delete_Polyhedron(Inv),
	union_sl(Ids,Ids2,Ids_join),
	merge_implied_summaries_aux(Multimap,(Inv2,Ids_join),Compressed_pair,Rest).
merge_implied_summaries_aux([(Inv2,Ids2)|Multimap],(Inv,Ids),Compressed_pair,Rest):-
	ppl_Polyhedron_contains_Polyhedron(Inv,Inv2),!,
	ppl_delete_Polyhedron(Inv2),
	union_sl(Ids,Ids2,Ids_join),
	merge_implied_summaries_aux(Multimap,(Inv,Ids_join),Compressed_pair,Rest).	
	
merge_implied_summaries_aux([(Inv2,Ids2)|Multimap],(Inv,Ids),Compressed_pair,[(Inv2,Ids2)|Rest]):-
	merge_implied_summaries_aux(Multimap,(Inv,Ids),Compressed_pair,Rest).		

generate_ppl_polyhedra_pairs(Vars,(Inv,Ids),(Handle,Ids)):-
	to_numbervars_nu( (Vars,Inv) , _, (_,Inv_ground), Dim),
	to_ppl_dim(c, Dim, Inv_ground, Handle).
	 
generate_contraints_pairs(Vars,(Handle,Ids),(Inv_normalized,Ids)):-
	from_ppl(c , Handle,_, Vars, Inv),
	nad_normalize_polyhedron(Inv,Inv_normalized).


get_all_pairs([],Accum_pairs,Accum_pairs).
get_all_pairs([Var_set|Vars_sets],Accum_pairs,All_pairs):-
	maplist(get_all_pairs_1(Vars_sets),Var_set,Sets),
	unions_sl([Accum_pairs|Sets],Accum_pairs1),
	get_all_pairs(Vars_sets,Accum_pairs1,All_pairs).

get_all_pairs_1(Set_list,Elem,Set_pairs):-
	maplist(get_all_pairs_2(Elem),Set_list,Sets_pairs),
	unions_sl(Sets_pairs,Set_pairs).
get_all_pairs_2(Elem,Set,Set_pairs):-
	maplist(sorted_tuple(Elem),Set,Pair_list),
	exclude(same_var_tuple,Pair_list,Pair_list1),
	from_list_sl(Pair_list1,Set_pairs).	



is_rational(N):-nonvar(N),number(N).
is_rational(N/M):-nonvar(N),number(N),number(M).

ground_copy(Term,Term_ground):-
	copy_term(Term,Term_ground),
	numbervars(Term_ground,0,_).

write_le_internal(Coeffs+C,Le):-
	maplist(write_coeffs,Coeffs,Coeffs1),
	write_sum(Coeffs1,Le_aux),
	(C==0->
	  Le=Le_aux
	  ;
	  (Le_aux==0->
	     Le=C
	     ; 
	     Le=Le_aux+C
	  )
	  ).	
write_coeffs((Var,Coeff),Coeff*Var).


%! repeat_n_times(+N:int,+Elem:A,-Elems:list(A)) is det
% generate a list with N copies of Elem
repeat_n_times(0,_,[]):-!.
repeat_n_times(N,Elem,[Elem|Is]):-
	N>0,
	N2 is N-1,
	repeat_n_times(N2,Elem,Is).

%! get_it_vars_in_loop(+Loop:loop_cost,-It_var:Var) is det
% obtain the iteration variable of Loop
%get_it_vars_in_loop(loop(It_var,_,_,_,_),It_var).

%! tuple(?A:A,?B:B,?C:(A,B))
% C is the pair (A,B).
% It can be used in any direction.
tuple(A,B,(A,B)).

sorted_tuple(X,Y,(X,Y)):-X @< Y,!.
sorted_tuple(X,Y,(Y,X)):-!.


same_var_tuple((X,Y)):-X==Y.

%! zip_with_op(?Op:atom,?C:A,?Term:atom(A,B))
% Term is Op(C).
% It can be used in any direction.
zip_with_op(Op,C,Term):-
	Term=..[Op,C].

%! zip_with_op2(?Op:atom,?C:A,?L:B,?Term:atom(A,B))
% Term is Op(C,L).
% It can be used in any direction.
zip_with_op2(Op,C,L,Term):-
	Term=..[Op,C,L].

%! assign_right_vars(+Xs:list((A,B)),+Right_vars:A,-Right_Xs:list(B)) is det
% Unify the first component of all the elements of Xs with Right_vars
% and return a list with the second elements Right_Xs
assign_right_vars([],_Right_vars,[]).
assign_right_vars([(Right_vars,X)|Xs],Right_vars,[X|Right_Xs]):-
 	assign_right_vars(Xs,Right_vars,Right_Xs).

:-meta_predicate bagof_no_fail(?,0,-).

%! bagof_no_fail(+A:term,+B:predicate,-C:list(term)) is det
% a deterministic version of bagof that does not fail
% but returns an empty list instead
bagof_no_fail(A,B,C):-bagof(A,B,C),!.
bagof_no_fail(_,_,[]).

:-meta_predicate foldr(3,+,+,-).

%! foldr(+Pred:predicate(A,B,A),+List:list(B), +Initial:A, -Result:A) is nondet
% Implements foldr/4 (with one list)
foldr(_Pred,[], Base, Base). 	
foldr(Pred,[X|Xs], Base, T):-
    call(Pred,Base,X,Base1),
	foldr(Pred,Xs,Base1,T).
	
:-meta_predicate sort_with(+,2,-).	
%! sort_with(+Xs_uns:list(A),+Bigger:predicate,-Xs:list(A)) is det
% sort a list Xs_uns into Xs according to the predicate Bigger
sort_with(Xs_uns,Bigger,Xs) :-
        qs(Xs_uns,Bigger,Xs,[]),
	!.

qs([],_Smaller, T, T).
qs([X | Xs],Smaller, S, T) :- pt(Xs, X,Smaller, L, G), qs(L,Smaller, S, [X | M]), qs(G,Smaller, M, T).

pt([], _,_, [], []).
pt([X | Xs], M,Smaller, L, [X | G]) :- 
	 call(Smaller,X,M),!,
    pt(Xs, M,Smaller, L, G).
pt([X | Xs], M,Smaller, [X | L], G) :- pt(Xs, M,Smaller, L, G).	


	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! normalize_constraint(+C:linear_constraint,-CN:linear_constraint) is det
% transform C into its normalized representation CN:
%
%  C1*X1+C2*X2+...CN*XN>= C0
normalize_constraint(C,CN):-
	constraint_to_coeffs_rep(C,Coeff_rep),  % this to lines normalize
	coeffs_rep_to_constraint(Coeff_rep,CN).

%! constraint_to_coeffs_rep(+Constr:linear_constraint, -Coeff_rep:coeff_rep(list(summand),relational_operator,int))  is det
% given a linear constraint, it generates a coefficient representation.
%
% Coeffs=[C1*X1, C2*X2,..., CN*XN] Rel='>=' and B=C0.
constraint_to_coeffs_rep(Constr, coeff_rep(Coeffs_sorted,Rel1,B)) :-
    Constr =.. [ Rel, L, R],
    is_relational(Rel),
   parse_le(L,L_exp),
   parse_le(R,R_exp),
   subtract_le(L_exp,R_exp,Le_x),
   % parse_le( L-R, Le_x),
    integrate_le(  Le_x, _Den, Coeffs_x + NegB), 
    maplist(tuple, Vars, Fracs,Coeffs_x),
     (Rel= '=<'->
        maplist(negate_fr,Fracs,Fracs1),
        NegB=B,
        Rel1= '>='
        ;
        Fracs=Fracs1,
        negate_fr( NegB, B),
        Rel1= Rel      
    ),
    maplist(zip_with_op2( '*'), Fracs1, Vars, Coeffs),
    from_list_sl(Coeffs,Coeffs_sorted).


is_relational( =<).
is_relational( = ).
is_relational( >=).

%! coeffs_rep_to_constraint(+Coeff_rep:coeff_rep(list(summand),relational_operator,int),-Constr:linear_constraint) is det
% given a coefficient representation of a linear constraint, generates the linear constraint.
% It is the inverse operarion of constraint_to_coeffs_rep/2.
coeffs_rep_to_constraint(coeff_rep(Coeffs,Op,B), Constraint) :-
	write_sum(Coeffs,Exp),
	Constraint =.. [ Op, Exp, B]. 

%! write_sum(Xs:list(A),Sum:sum(A)) is det
% create a term that is the sum of the elements of the list
% with right associativity
write_sum([],0).
write_sum([X|Xs],Sum):-
	exclude(zero,Xs,Xss),
	foldr(zip_with_op2('+'),Xss,X,Sum).
write_product([],0).
write_product([X|Xs],Sum):-
	foldr(zip_with_op2('*'),Xs,X,Sum).
	
zero(X):-X==0.

%! normalize_constraint_wrt_var(C,Var,NC) is det
% given C:=C1*Var+C2*X2+...CN*XN>= C0, express the constraint in terms of Var:
%
% NC:= Var =< C2/C1*X2 +...CN/C1*XN -C0/C1 if C1>=0
%
% NC:= Var >= C2/C1*X2 +...CN/C1*XN -C0/C1 if C1<0
normalize_constraint_wrt_var(C,Var,NC) :-
	constraint_to_coeffs_rep(C,coeff_rep(Coeffs,Op,B)),
	get_var_coeff(Coeffs,Var,Var_Coeff,Other_Coeffs),
	Var_Coeff_aux is -1*Var_Coeff,
	divide_coeffs(Other_Coeffs,Var_Coeff_aux,Coeffs_aux),
	divide_fr(B,Var_Coeff,B_aux),
	( Var_Coeff > 0 -> Op_aux = Op ; reverse_op(Op,Op_aux)),
	write_sum(Coeffs_aux,Exp),
	(   B_aux == 0 -> Exp_aux = Exp
	;   Coeffs_aux == [] -> Exp_aux = B_aux
	;   Exp_aux = Exp+B_aux
	),
	NC =.. [Op_aux, Var, Exp_aux].
	
	
normalize_constraint_wrt_vars(C,Vars,NC) :-
	constraint_to_coeffs_rep(C,coeff_rep(Coeffs,Op,B)),
	partition(coeff_contains_var(Vars),Coeffs,Coeffs_its,Coeffs_vars),
	Coeffs_its=[_|_],
	(maplist(positive_coeff,Coeffs_its)->
		maplist(negate_coefficient,Coeffs_vars,Coeffs_vars_neg),
		
		maplist(get_coeff_components,Coeffs_its,[Factor1|Factors],Its),
		foldl(gcd_fr,Factors,Factor1,GCD),
		divide_coeffs(Coeffs_vars_neg,GCD,Coeffs_vars_neg_div),
		divide_fr(B,GCD,B_div),
		write_sum(Coeffs_vars_neg_div,Exp),
		NC =.. [Op, Its, Exp+B_div]
	;
	maplist(negative_coeff,Coeffs_its),
	%Fail if we have mixed coefficients
		maplist(negate_coefficient,Coeffs_its,Coeffs_its_neg),
		maplist(get_coeff_components,Coeffs_its_neg,[Factor1|Factors],Its),
		foldl(gcd_fr,Factors,Factor1,GCD),
		divide_coeffs(Coeffs_vars,GCD,Coeffs_vars_div),
		divide_fr(B,GCD,B_div),
		negate_fr(B_div,B_div_neg),
		write_sum(Coeffs_vars_div,Exp),
		reverse_op(Op,Op_aux),
		NC =.. [Op_aux, Its, Exp+B_div_neg]
	).

relax_constraint_with_its(Its,Constraint,Constraint1):-
	%FIXME ignoring equal for now
	constraint_to_coeffs_rep(Constraint, coeff_rep(Coeffs,>=,B)),
	partition(coeff_contains_var(Its),Coeffs,Coeffs_its,Coeffs_vars),
	maplist(positive_coeff,Coeffs_its),!,
	coeffs_rep_to_constraint(coeff_rep(Coeffs_vars,>=,B),Constraint1).
	
relax_constraint_with_its(Its,Constraint,Constraint):-
	%FIXME ignoring equal for now
	constraint_to_coeffs_rep(Constraint, coeff_rep(Coeffs,=,_B)),
	partition(coeff_contains_var(Its),Coeffs,Coeffs_its,_Coeffs_vars),
	Coeffs_its=[],!.	
relax_constraint_with_its(Its,Constraint,Constraint):-
	%FIXME ignoring equal for now
	constraint_to_coeffs_rep(Constraint, coeff_rep(Coeffs,=<,_B)),
	partition(coeff_contains_var(Its),Coeffs,Coeffs_its,_Coeffs_vars),
	Coeffs_its=[],!.	
relax_constraint_with_its(_Its,_Constraint,[]).

get_coeff_components(C*V,C,V).	
coeff_contains_var(Vars,_C * Var):-
	contains_sl(Vars,Var).
negate_coefficient(C* Var,C_neg * Var):-
	negate_fr(C,C_neg).	
	
positive_coeff(Fr * _):-
   geq_fr(Fr,0).	
negative_coeff(Fr * _):-
   geq_fr(0,Fr).
   
reverse_op(>=,=<).
reverse_op(=<,>=).
reverse_op(=,=).

divide_coeffs([],_,[]).
divide_coeffs([N*V|Vs],Factor,[NF*V|FVs]) :-
	divide_fr(N,Factor,NF),
	divide_coeffs(Vs,Factor,FVs).	


get_var_coeff([N*V|Cs],Var,N,Cs)    :- V == Var, !.
get_var_coeff([V|Cs],Var,N,[V|OCs]) :- get_var_coeff(Cs,Var,N,OCs).






	