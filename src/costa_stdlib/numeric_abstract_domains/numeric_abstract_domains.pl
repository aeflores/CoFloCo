/*
    Copyright (C) 2009  E.Albert, P.Arenas, S.Genaim, G.Puebla, and D.Zanardini
                        https://costa.ls.fi.upm.es

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

/** <module> A common interface to the different libraries of nummeric 
abstract domains, that can be used for handling systems of linear constraints. 

The Nummeric abstract domain is a class NAD of types T that provide the 
following operations: 
  * top : A
  * bottom: A
  * lub : A -> A -> A
  * glb : A -> A -> A
  * is_top: A -> Bool
  * is_consistent : A -> Bool
  * leq: A -> A -> Bool
  * import: Constraint_System -> A
  * export: A -> Constraint_System
  * normalize: A -> A
  * project :  list<Var> -> A -> A
  * widening:   A -> A -> A
  * narrowing:  A -> A -> A

Such that ( A, leq, lub, glb, top, bottom) is a lattice. 

In order to facilitate its use, we also add a couple of operations for 
importing or exporting the values of the NAD type A from a common 
representation as a System of Linear Constraints. 

@author
@license GPL
*/

:- module(numeric_abstract_domains,[
    nad_available_domain/1,
    nad_current_domain/1,
    nad_set_domain/1,
    nad_initialize/0,
    
    nad_true/1,
    nad_false/1,
    nad_import/2,
    nad_import_list/2,
    nad_import_disjunct_list/2,
    nad_export/2,
    nad_export_list/2,
    nad_export_disjunct_list/2,

    nad_is_top/1,
    nad_is_bottom/1,
    nad_leq/2,
    nad_equals/2,
    
    nad_consistent_constraints/1, 

    nad_normalize/2,
    nad_project/3,
    nad_project_list/3,

    nad_equivalent/3,
    nad_entails/3, 
    nad_lub/6, 
    nad_glb/3, 
    nad_difference/3,
    
    nad_list_lub/2,
    nad_list_glb/2,
    nad_add_constraints/3,
    
    nad_widen/5, 
    nad_solve/3,
    nad_minimize/3, 
    nad_maximize/3, 
    nad_write/2,
    nad_write_list/2,
    
    nad_separate_disjuncts/2,
    nad_compare_linear_expressions/4,

    nad_ranking_function_MS/4,
    nad_ranking_function_PR/4,
    nad_all_ranking_functions_MS/4,
    nad_all_ranking_functions_PR/4
    
]).

:- use_module(stdlib(utils),[ut_varset/2]). 
/*
The fact nad_current_domain is a global fact-variable that indicates on which 
domain is Costa actually working. 
*/
:- dynamic nad_current_domain/1.

:- include('nad-default.pl').


nad_set_domain(Dom) :-
	nad_available_domain(Dom),
	retractall(nad_current_domain(_)),
	assertz(nad_current_domain(Dom)).

nad_initialize :-
	nad_current_domain(Dom),
	nad_initialize_aux(Dom).

/*
nad(N) => nad_true( Top:N). 

Top is the top element of the nummeric abstract domain N, 
which corresponds to the logical value true. 
*/
nad_true( Top ) :-
    nad_current_domain(Dom), 
    nad_true_aux(Dom,Top). 

/*
nad(N) => nad_false( Bot:N). 

Bot is the bottom element of the nummeric abstract domain N, 
which corresponds to the logical value false. 
*/
nad_false(Bot) :-
	nad_current_domain(Dom),
	nad_false_aux(Dom,Bot).

/*
nad(N) => nad_is_top( + Phi : N ) is semidet.

True if Phi is the top element in the numeric abstract domain.
*/
nad_is_top( Phi) :- 
    nad_current_domain( Dom), 
    nad_is_top_aux( Dom, Phi).

/*
nad(N) => nad_is_bottom( + Phi : N ) is semidet.

True if Phi is the bottom element in the numeric abstract domain.
*/
nad_is_bottom( Phi) :- 
    nad_current_domain( Dom), 
    nad_is_bottom_aux( Dom, Phi).

/*
nad(N) => nad_equals( + APhi : N , + BPhi : N ) is semidet.

*/
%nad_equals( APhi, BPhi) :- 
%    nad_current_domain( Dom), 
%    nad_equals_aux( Dom, APhi, BPhi).
nad_equals( APhi, BPhi) :- 
    nad_current_domain( Dom), 
    ut_varset( (APhi,BPhi), Vars), 
    nad_equivalent_aux( Dom, Vars, APhi, BPhi).

/*
nad(N) => nad_leq( + APhi : N , + BPhi : N ) is semidet.

*/

%nad_leq( APhi, BPhi) :- 
%    nad_current_domain( Dom), 
%    nad_leq_aux( Dom, APhi, BPhi).
nad_leq( APhi, BPhi) :- 
    nad_current_domain( Dom), 
    ut_varset( (APhi,BPhi), Vars), 
    nad_entails_aux( Dom, Vars, APhi, BPhi).
    

/*
nad(N) => nad_equivalent( 
    + Vars:list<var> , + A_Elem:N , + B_Elem:N
) is semidet. 

true if the absract elements Elem_A and Elem_B are equivalent. 

Every instance of nad(N) should guarantee that nad_equivalent is an equivalence
relationship: it must be reflexive, simmetric and transitive.  
*/
nad_equivalent( Vars, A_Elem , B_Elem) :- 
    nad_current_domain(Dom),
    nad_equivalent_aux( Dom, Vars, A_Elem, B_Elem ).

/*
nad(N) => nad_entails( 
    + Vars: list<var>, + A_Elem: N, + B_Elem: N
) is semidet. 

True if A_Elem implies B_Elem. 
*/
nad_entails( Vars, A_Elem, B_Elem ) :-
    nad_current_domain( Dom ),
    nad_entails_aux( Dom, Vars, A_Elem, B_Elem ).


/*
nad(N) => nad_lub( 
    + A_Vars:list<var>,  + A_Elem:N, 
    + B_Vars:list<var>,  + B_Elem:N, 
    - Lub_Vars:list<var>,- Lub_Elem:N ) is det.  

Lub_Elem is the least upper bound of Elem_A and Elem_B. 
This operation is also called join, and in the logical interpretation 
it corresponds to the "or" operation. 
*/
nad_lub(A_Vars, A_Elem, B_Vars, B_Elem, Lub_Vars, Lub_Elem) :-
    nad_current_domain(Dom),
    nad_lub_aux(Dom,A_Vars, A_Elem, B_Vars, B_Elem, Lub_Vars, Lub_Elem).

    

/*
nad(N) => nad_glb( + A_Elem:N, + B_Elem:N, - Glb_Elem:N ) is det.  

Lub_Elem is the greatest lower bound of Elem_A and Elem_B. 
This operation is also called meet, and in the logical interpretation 
it corresponds to the "and" operation.                    
*/
nad_glb(A_Elem, B_Elem, Glb) :-
    nad_current_domain(Dom),
    nad_glb_aux(Dom,A_Elem, B_Elem, Glb).

    

/*
nad(N) => nad_difference( +ANae:N, + BNae:N, - Diff:N) is det.
*/
nad_difference(AElem, BElem, Diff) :- 
    nad_current_domain(Dom),
    nad_difference_aux(Dom, AElem, BElem, Diff).
    


/*
nad(N) => nad_list_lub( +Elems:list<N>,  - Lub_Elem:N) is det. 

Obtains the lub of all the abstract elements on the list. 
*/
nad_list_lub( Elems, Lub_Elem) :- 
    nad_current_domain(Dom), 
    nad_list_lub_aux(Dom, Elems, Lub_Elem).

    


/*
nad(N) => nad_list_lub( +Elems:list<N>,  - Lub_Elem:N) is det. 

Obtains the lub of all the abstract elements on the list. 
*/
nad_list_glb( Elems, Glb_Elem) :-
    nad_current_domain(Dom),
    nad_list_glb_aux(Dom, Elems, Glb_Elem).

    

/*
nad(N) => nad_import ( + Cs:Constraint_System , - Elem:N). 

Imports a Constraint System into an Element of the Abstract Domain N.
The abstract domains must follow an over-approximation semmantics: 
Elem is an overapproximation of the set of solutions of Cs.  

In the context of Abstract Interpretation, the import function can be seen as 
the abstraction function (usually written with a lowercase alpha) 
from the domain of conjunctive linear constraint systems. 
*/
nad_import(Cs, Nad_Cs) :- 
    nad_current_domain(Dom), 
    nad_import_aux(Dom, Cs, Nad_Cs). 

/*
nad_import_list( Css, Nad_Css) 

*/
nad_import_list( [], []). 
nad_import_list( [ Cs | Css] , [Phi | Phis] ) :- 
    nad_import(Cs, Phi), 
    nad_import_list( Css, Phis). 

/*
nad(N) => nad_import_disjunct_list( +  Css:list<constraint_system>, - Phi:N).
*/
nad_import_disjunct_list( Css, Phi ) :- 
    nad_import_list(Css, Phis), 
    nad_list_lub( Phis, Phi).

    

/*
nad(N) => nad_export( + Elem: N , - Cs: Constraint_System). 

Exports an Element of the current astract domain N into a Constraint System.
The exporting always follows an over-approximation semmantics: 
Cs is an overapproximation of the set of solutions of Elem.  

In the context of Abstract Interpretation, the export function can be seen as 
the concretization function (usually written with a lowercase gamma) 
to the domain of conjunctive linear constraint systems to the current domain. 
*/
nad_export(Nad_Cs, Cs) :- 
    nad_current_domain(Dom), 
    nad_export_aux(Dom, Nad_Cs, Cs).

/*
nad(N) => nad_export_list( + Nads:list<N>, - Css: list<constraint_system>).
 
*/
nad_export_list( [], []).
nad_export_list( [Nae|Naes], [Cs|Css]) :- 
    nad_export( Nae, Cs), 
    nad_export_list(Naes, Css).

nad_export_disjunct_list( Phi, Css) :- 
    nad_separate_disjuncts( Phi, Phis), 
    nad_export_list( Phis, Css). 

/*
nad(N) => nad_normalize( + Elem:N , - Nor_Elem:N).

Obtains from the element Elem of the current abstract domain another element 
Nor_Elem that is equivalent to Elem but is in some "simpler" or "normal" form.

*/
nad_normalize(Elem,Normal_Elem) :-
    nad_current_domain(Dom),
    nad_normalize_aux(Dom,Elem,Normal_Elem).


/*
nad(N) => nad_project( + Vars:list<var> , + Elem:N, - Proj_Elem:N).

Projects the abstract element Elem on the list of variables Vars. 
That means that Proj_Elem is another element of the abstract type N such that 
for every solution of Vars in Proj_Elem there is a solution of Vars in Elem. 

*/
nad_project(Vars,Elem,Proj_Elem) :-
	nad_current_domain(Dom),
    nad_project_aux(Dom,Vars,Elem,Proj_Elem).

	

/*
nad_project_list( Nads, Vars, Proj_Nads) 
*/
nad_project_list( [], _Vars, []).
nad_project_list( [Phi|Phis], Vars, [NPhi|NPhis] ) :- 
    nad_project( Vars, Phi, NPhi), 
    nad_project_list( Phis, Vars, NPhis ).


/*
nad(N) => nad_consistent_constraints( + Elem:N) is semidet. 

True if Elem is different from the bottom element of the abstract domain.
*/
nad_consistent_constraints(Cs) :-
	nad_current_domain(Dom),
	nad_consistent_constraints_aux(Dom,Cs).
    

/*
nad_widen
*/
nad_widen( Vars, Small, Big, W_Vars, Widen ) :-
	nad_current_domain( Dom ),
	nad_widen_aux( Dom, Vars, Small, Big, W_Vars, Widen ).

/* nad_solve*/
nad_solve( Cs, Vars, Vals) :-
    nad_current_domain( Dom),
    nad_solve_aux( Dom, Cs, Vars, Vals). 
/*
nad_minimize
*/
nad_minimize( Cs, Vars, Ms ) :-
	nad_current_domain( Dom ),
	nad_minimize_aux( Dom, Cs, Vars, Ms ).

/*
nad_maximize
*/
nad_maximize( Cs, Vars, Ms ) :-
	nad_current_domain( Dom ),
	nad_maximize_aux( Dom, Cs, Vars, Ms ).

/*
nad_add_constraints
*/
nad_add_constraints( Cs, Consts, NCs ) :- 
    nad_import( Consts, Cs1 ),
    nad_glb( Cs, Cs1, NCs ).

/*
nad(N) => nad_write( + Cs , - WCs) 

"Pretty-prints" the abstract element Cs as WCs.
*/
nad_write( Cs, WCs ) :- 
    nad_current_domain( Dom ),
    nad_write_aux(Dom, Cs, WCs ). 

nad_write_list( [], []).
nad_write_list( [Cs|Css], [WCs|WCss] ) :- 
    nad_write( Cs, WCs ), 
    nad_write_list( Css, WCss ). 

/*
nad(N) => nad_separate_disjuncts( + Cs: N, - Disjs:list<N> ) 

*/
nad_separate_disjuncts( Cs, Ds ) :- 
    nad_current_domain( Dom ), 
    nad_disjuncts_aux( Dom, Cs, Ds ). 



/*
nad(N) => nad_compare_linear_expressions( 
    + Phi:N, + AExp:linear_exp, + BExp:linear_exp, - Result:result
) is det.

It compares the linear expressions AExp and BExp under the context Phi, and
gives a Result which is one of the following:
- One of the operators '=<', '=' , '>=' with the obvious meaning. 
- none, which means AExp and BExp are not comparable.

Unlike in the compare predicate for integers, this predicate doesn't return
strict comparison operators. 
*/
nad_compare_linear_expressions( Phi, ExpA, ExpB, Result) :-
    ut_varset( f(ExpA,ExpB), Vars),
    nad_import( [ExpA =< ExpB], Leq),
    nad_import( [ExpA >= ExpB], Geq),
    ( nad_entails( Vars, Phi, Leq)
    ->( nad_entails( Vars, Phi, Geq) 
        ->  Result = '='
        ;   Result = '=<'
    );( nad_entails( Vars, Phi, Geq)
        ->  Result = '>='
        ;   Result = none
    )).

/*
 nad_ranking_function_XX( 
    + Cs:Polyhedra, + EntryVars:list<var>,  + ExitVars:list<var>, - Rf:linear_expression)

This predicate receives a polyhedra representing a loop, the list of variables at the entry of the
loop, the list of variables at the exit of the loop and returns (if it exits) a linear expression
  that is a ranking function of the loop. The Rf is expressed in terms of the entry variables.
*/
nad_ranking_function_MS(Cs,EntryVars,ExitVars,Rf):-
	nad_current_domain( Dom ), 
	nad_ranking_function_MS_aux(Dom,EntryVars,ExitVars,Cs,Rf).
nad_ranking_function_PR(Cs,EntryVars,ExitVars,Rf):-
	nad_current_domain( Dom ), 
	nad_ranking_function_PR_aux(Dom,EntryVars,ExitVars,Cs,Rf).
/*
 nad_all_ranking_functions_XX( 
    + Cs:Polyhedra, + EntryVars:list<var>,  + ExitVars:list<var>, - Rfs:list<linear_expressions>)

This predicate receives a polyhedra representing a loop, the list of variables at the entry of the
loop, the list of variables at the exit of the loop and returns (if it exits) a list of
 possible linear ranking functions of the loop.
*/
nad_all_ranking_functions_MS(Cs,EntryVars,ExitVars,Rfs):-
	nad_current_domain( Dom ), 
	nad_all_ranking_functions_MS_aux(Dom,EntryVars,ExitVars,Cs,Rfs).
nad_all_ranking_functions_PR(Cs,EntryVars,ExitVars,Rfs):-
	nad_current_domain( Dom ), 
	nad_all_ranking_functions_PR_aux(Dom,EntryVars,ExitVars,Cs,Rfs).

 



:- discontiguous nad_available_domain/1.
:- discontiguous nad_initialize_aux/1.
:- discontiguous nad_true_aux/2.
:- discontiguous nad_false_aux/2.
:- discontiguous nad_is_top_aux/2.
:- discontiguous nad_is_bottom_aux/2.
:- discontiguous nad_equals_aux/3.
:- discontiguous nad_leq_aux/3.
:- discontiguous nad_lub_aux/7.
:- discontiguous nad_glb_aux/4.
:- discontiguous nad_difference_aux/4.
:- discontiguous nad_list_lub_aux/3.
:- discontiguous nad_list_glb_aux/3.
:- discontiguous nad_normalize_aux/3.
:- discontiguous nad_project_aux/4.
:- discontiguous nad_consistent_constraints_aux/2.
:- discontiguous nad_entails_aux/4.
:- discontiguous nad_equivalent_aux/4.
:- discontiguous nad_widen_aux/6.
:- discontiguous nad_solve_aux/4.
:- discontiguous nad_minimize_aux/4.
:- discontiguous nad_maximize_aux/4.
:- discontiguous nad_import_aux/3.
:- discontiguous nad_export_aux/3.
:- discontiguous nad_write_aux/3.
:- discontiguous nad_disjuncts_aux/3.
:- discontiguous nad_ranking_function_MS_aux/5.
:- discontiguous nad_ranking_function_PR_aux/5.
:- discontiguous nad_all_ranking_functions_MS_aux/5.
:- discontiguous nad_all_ranking_functions_PR_aux/5.



:- include('nad-available_domains.pl').


nad_is_top_aux(_,_).    % FIXME remove
nad_is_bottom_aux(_,_). % FIXME remove
