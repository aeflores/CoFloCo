

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

:- module(numeric_abstract_domains_efficient,[
    nad_initialize/0,
    nad_import/2,
%    nad_export/2,
    nad_leq/2,
    nad_consistent_constraints/1, 
    nad_normalize/2,
    nad_project/3,
    nad_project_special/3,
    get_permanent_polyhedra/2,
    discard_permanent_polyhedra/1,
    nad_entails/3, 
    nad_lub/6, 
    nad_glb/3, 
   
    nad_list_lub/2,
    nad_list_glb/2,
    nad_add_constraints/3, 
    nad_widen/5, 
    nad_ranking_function_MS/4,
    nad_ranking_function_PR/4,
    nad_all_ranking_functions_MS/4,
    nad_all_ranking_functions_PR/4
    
]).
:- use_module(stdlib(numvars_util)).
:- use_module(stdlib(set_list)).
:- use_module(stdlib(utils),[ut_varset/2]). 
:- use_module(stdlib(linear_constraint_system),[
    parse_lcs/2,
    write_natural_lcs/2
]). 
 :- use_module(stdlib(ppl),[
     ppl_initialize/0, 
     ppl_Polyhedron_remove_higher_space_dimensions/2,
     ppl_Pointset_Powerset_C_Polyhedron_remove_higher_space_dimensions/2,
     ppl_Polyhedron_upper_bound_assign/2,
     ppl_Pointset_Powerset_C_Polyhedron_upper_bound_assign/2, 
     ppl_Polyhedron_H79_widening_assign/2,
     ppl_Pointset_Powerset_C_Polyhedron_BHZ03_H79_H79_widening_assign/2,    
     ppl_delete_Pointset_Powerset_C_Polyhedron/1,
     ppl_Polyhedron_contains_Polyhedron/2,
     ppl_Pointset_Powerset_C_Polyhedron_geometrically_covers_Pointset_Powerset_C_Polyhedron/2, 
     ppl_Polyhedron_is_empty/1,
     ppl_Pointset_Powerset_C_Polyhedron_is_empty/1,
    ppl_Polyhedron_minimize/5,
     ppl_Polyhedron_add_constraints/2,
     ppl_Pointset_Powerset_C_Polyhedron_minimize/5,
     ppl_Pointset_Powerset_C_Polyhedron_add_constraints/2,
     ppl_Polyhedron_maximize/5,
     ppl_Pointset_Powerset_C_Polyhedron_maximize/5,
     ppl_new_C_Polyhedron_from_constraints/2,
     ppl_new_NNC_Polyhedron_from_constraints/2,
     ppl_new_C_Polyhedron_from_space_dimension/3,
     ppl_new_NNC_Polyhedron_from_space_dimension/3,
     ppl_new_Pointset_Powerset_C_Polyhedron_from_space_dimension/3,
     ppl_Pointset_Powerset_C_Polyhedron_pairwise_reduce/1,
     ppl_Pointset_Powerset_C_Polyhedron_omega_reduce/1,
     ppl_Pointset_Powerset_C_Polyhedron_add_disjunct/2,
     ppl_Polyhedron_get_constraints/2,
 ppl_Polyhedron_get_minimized_constraints/2,
     ppl_Polyhedron_get_generators/2,			   
     ppl_Pointset_Powerset_C_Polyhedron_size/2,
     ppl_Pointset_Powerset_C_Polyhedron_begin_iterator/2,
     ppl_delete_Pointset_Powerset_C_Polyhedron_iterator/1,
     ppl_Pointset_Powerset_C_Polyhedron_get_disjunct/2,
     ppl_Pointset_Powerset_C_Polyhedron_increment_iterator/1,
     ppl_delete_Polyhedron/1,
     ppl_delete_Pointset_Powerset_C_Polyhedron/1, 
    ppl_Pointset_Powerset_C_Polyhedron_intersection_assign/2, 
    ppl_Polyhedron_intersection_assign/2, 
     ppl_Polyhedron_difference_assign/2,
     ppl_Pointset_Powerset_C_Polyhedron_difference_assign/2,
     ppl_Polyhedron_equals_Polyhedron/2, 
     ppl_Pointset_Powerset_C_Polyhedron_geometrically_equals_Pointset_Powerset_C_Polyhedron/2,

 	  ppl_termination_test_MS_C_Polyhedron/1,
 	  ppl_termination_test_PR_C_Polyhedron/1,
 	  ppl_one_affine_ranking_function_MS_C_Polyhedron/2,
 	  ppl_one_affine_ranking_function_PR_C_Polyhedron/2,
 	  ppl_all_affine_ranking_functions_MS_C_Polyhedron/2,
 	  ppl_all_affine_ranking_functions_PR_C_Polyhedron/2,
 	  ppl_new_C_Polyhedron_from_C_Polyhedron/2,
 	  ppl_Polyhedron_add_space_dimensions_and_embed/2,
 	  ppl_Polyhedron_remove_space_dimensions/2
 ]).
 
nad_initialize :-
    load_foreign_library('libppl_swiprolog.so'),	
	ppl_initialize.

/*
nad(N) => nad_leq( + APhi : N , + BPhi : N ) is semidet.

*/

%nad_leq( APhi, BPhi) :- 
%    nad_current_domain( Dom), 
%    nad_leq_aux( Dom, APhi, BPhi).
nad_leq( APhi, BPhi) :- 
    ut_varset( (APhi,BPhi), Vars), 
    nad_entails( Vars, APhi, BPhi).
/*
nad(N) => nad_entails( 
    + Vars: list<var>, + A_Elem: N, + B_Elem: N
) is semidet. 

True if A_Elem implies B_Elem. 
*/

nad_entails(Vars,Clist1,Clist2) :-
    to_numbervars_nu(f(Vars,Clist1,Clist2),_, f(_,Clist1_x,Clist2_x),Dim), 
    to_ppl_dim( Dim, Clist1_x, Handle_1), 
    to_ppl_dim( Dim, Clist2_x, Handle_2), 
    ( ppl_Polyhedron_contains_Polyhedron(Handle_1, Handle_2)
        ->  R=entails
        ;   R=does_no_entail
    ),
    dispose(Handle_1),
    dispose(Handle_2),
    !,
    R= entails.

get_permanent_polyhedra(Phi,permanent_poly(Vars,Handle)):-
	term_variables(Phi,Vars),
	to_numbervars_nu(f(Vars,Phi),_, f(_,Phi_x),Dim), 
    to_ppl_dim( Dim, Phi_x, Handle).

discard_permanent_polyhedra(permanent_poly(_Vars,Handle)):-
	dispose(Handle).

/*
ppl_lub(+Xs, +Cxs, +Ys, +Cys, +Zs, +Czs) : 

 * Xs and Ys are list of variables of the same length, 
 * Cxs and Cys are lists of constraints of the variables of Xs and
   Ys repressively, 
 * Zs is a list of new fresh variables of the same length as Xs and Ys,
 * Czs is a list of constrains over Zs which represents the lub operation  
   of Cxs and Cys as elements of Type.
*/
nad_lub( Xs, Cxs, Ys, Cys, Zs, Czs) :-
    copy_term( f(Xs,Ys,Cxs,Cys),f(Vs_x,Vs_x,Cxs_x,Cys_x) ),
    numbervars([Vs_x],0,Dim),
    to_ppl_dim( Dim, Cxs_x, Handle_x), 
    to_ppl_dim( Dim, Cys_x, Handle_y), 

    ppl_Polyhedron_upper_bound_assign(Handle_x,Handle_y),
    from_ppl( Handle_x, Dim, Zs, Czs), 
    dispose(Handle_x),
    dispose(Handle_y).


/*
ppl_glb(+ +Cxs, +Cys, -Glb) : 

 * Cxs and Cys are lists of constraints of the variables 
 * Glb is the Ppl object that represents the the greatest lower bound 
    of Cxs and Cys as elements of Type.
*/
nad_glb( Elem_A, Elem_B, Glb) :-
    to_numbervars_nu( (Elem_A, Elem_B), Vars, (Elem_Ax, Elem_Bx), Dim), 
    to_ppl_dim( Dim, Elem_Ax, Handle_x), 
    to_ppl_dim( Dim, Elem_Bx, Handle_y), 
    ppl_Polyhedron_intersection_assign(Handle_x,Handle_y),
    from_ppl(Handle_x, Dim, Vars, Glb), 
    dispose(Handle_x),
    dispose(Handle_y).

/*
nad(N) => nad_list_lub( +Elems:list<N>,  - Lub_Elem:N) is det. 

Obtains the lub of all the abstract elements on the list. 
*/

nad_list_lub(  Elems, Lub) :- 
    to_numbervars_nu( Elems, Vars, Elems_x, Dim), 
    ppl_new_C_Polyhedron_from_space_dimension(Dim, empty, Handle),
    list_lub_x( Elems_x, Dim, Handle),
    from_ppl( Handle, Dim, Vars, Lub), 
    dispose(Handle).
    
list_lub_x( [], _Dim, _Handle ) . 
list_lub_x( [Elem|Elems], Dim,  Handle) :-
    list_lub_xx( Elem, Dim, Handle), 
    list_lub_x( Elems, Dim, Handle).

list_lub_xx( Elem, Dim, Handle) :- 
    to_ppl_dim( Dim, Elem, Handle_x), 
    ppl_Polyhedron_upper_bound_assign(Handle,Handle_x),
    dispose(Handle_x). 


ppl_list_glb( Elems, Glb) :- 
    to_numbervars_nu( Elems, Vars, Elems_x, Dim), 
    ppl_new_C_Polyhedron_from_space_dimension(Dim, universe, Handle),
    list_glb_x( Elems_x,  Dim, Handle),
    from_ppl( Handle, Dim, Vars, Glb), 
    dispose( Handle).
    
list_glb_x( [], _Dim, _Handle ). 
list_glb_x( [Elem|Elems],  Dim, Handle) :-
    list_glb_xx( Elem,  Dim, Handle), 
    list_glb_x(Elems,  Dim, Handle).

list_glb_xx( Elem,  Dim, Handle) :- 
    to_ppl_dim( Dim, Elem, Handle_x), 
    glb_x(  Handle, Handle_x), 
    dispose(  Handle_x).
    

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

nad_import(Cs, Import_Cs) :- 
    nonvar(Cs),
    parse_lcs(Cs, LCS),
    write_natural_lcs(LCS, Import_Cs).
/*
nad_import_list( Css, Nad_Css) 

*/
nad_import_list( [], []). 
nad_import_list( [ Cs | Css] , [Phi | Phis] ) :- 
    nad_import(Cs, Phi), 
    nad_import_list( Css, Phis). 


/*
nad(N) => nad_normalize( + Elem:N , - Nor_Elem:N).

Obtains from the element Elem of the current abstract domain another element 
Nor_Elem that is equivalent to Elem but is in some "simpler" or "normal" form.

*/

nad_normalize(Cs, NCs) :- 
    to_numbervars_nu( Cs, Vars, Cs_x, Dim),
    to_ppl_dim(Dim, Cs_x,Handle),
    from_ppl_minimized(Handle, Dim, Vars, NCs). 
/*
nad(N) => nad_project( + Vars:list<var> , + Elem:N, - Proj_Elem:N).

Projects the abstract element Elem on the list of variables Vars. 
That means that Proj_Elem is another element of the abstract type N such that 
for every solution of Vars in Proj_Elem there is a solution of Vars in Elem. 

*/


nad_project(Vars, Elem,Proj_Elem) :-
    to_numbervars_nu( f(Vars,Elem), _, f(_,Elem_x), Dim),
    to_ppl_dim( Dim, Elem_x, Handle),
    length(Vars,Proj_Dim),
    ppl_Polyhedron_remove_higher_space_dimensions(Handle,Proj_Dim),
    from_ppl( Handle, Proj_Dim, Vars, Proj_Elem),
    dispose(Handle).

nad_project_special([R|Vars_of_Interest],[Exp|permanent_poly(Vars,Handle)],Proj_Elem):-trace,
	ppl_new_C_Polyhedron_from_C_Polyhedron(Handle,Handle2),
	ppl_Polyhedron_add_space_dimensions_and_embed(Handle2,1),
	to_numbervars_nu( f(Vars,R,Vars_of_Interest,Exp), _, f(Vars_x,R_x,Vars_of_interest_x,Exp_x), Dim),
    to_ppl_dim( Dim, [Exp_x], Handle_x), 
    ppl_Polyhedron_intersection_assign(Handle_x,Handle2),
    from_list_sl([R_x | Vars_of_interest_x],Rem_vars),
    from_list_sl(Vars_x,All_vars),
    difference_sl(All_vars,Rem_vars,Remove_vars),
    ppl_Polyhedron_remove_space_dimensions(Handle_x,Remove_vars),
    length(Rem_vars,Proj_Dim),
    from_list_sl([R|Vars_of_Interest],Out_vars),
    from_ppl( Handle_x, Proj_Dim, Out_vars, Proj_Elem).


nad_project_special(Vars,Elem,Proj_Elem):-
   	nad_project(Vars, Elem,Proj_Elem).
/*
nad(N) => nad_consistent_constraints( + Elem:N) is semidet. 

True if Elem is different from the bottom element of the abstract domain.
*/

nad_consistent_constraints(Cs) :-
    to_numbervars_nu( Cs, _Vars, Cs_aux, Dim), 
    to_ppl_dim(Dim, Cs_aux,Handle_Cs),
    (ppl_Polyhedron_is_empty(Handle_Cs) -> R=empty ; R=not_empty),
    dispose(Handle_Cs),
    !,
    R=not_empty.
    


/*
nad_widen
*/
nad_widen(Vars,Clist1,Clist2,WidenVars,ClistWiden) :-
    to_numbervars_nu([Vars,Clist1,Clist2],_,[_,Clist1_x,Clist2_x],Dim),
    to_ppl_dim( Dim, Clist1_x, Handle_1),
    to_ppl_dim( Dim, Clist2_x, Handle_2),
    ppl_Polyhedron_H79_widening_assign(Handle_2,Handle_1),
    from_ppl(Handle_2, Dim, WidenVars,ClistWiden), 
    dispose(Handle_1),
    dispose(Handle_2).

/*
nad_add_constraints
*/
nad_add_constraints( Cs, Consts, NCs ) :- 
    nad_import( Consts, Cs1 ),
    nad_glb( Cs, Cs1, NCs ).


% Mesnard and Serebrenik method to obtain a single ranking function
nad_ranking_function_MS(EntryVars,ExitVars,Cs,Sym_Rf) :-
    copy_term( (ExitVars,EntryVars, Cs), (ExitVars_aux,EntryVars_aux, Cs_aux) ),
    append(ExitVars_aux,EntryVars_aux,Vars_aux),
    numbervars( Vars_aux,0,Dim),
    to_ppl_dim(Dim, Cs_aux,Handle_Cs),
    ppl_one_affine_ranking_function_MS_C_Polyhedron(Handle_Cs,point(Rf)),
    from_numbervars_nu(EntryVars,(ExitVars_aux,Rf),(_,Sym_Rf)),
    dispose(Handle_Cs).

%Podelski and Rybalchenko method to obtain a single ranking function
nad_ranking_function_PR(EntryVars,ExitVars,Cs,Sym_Rf) :-
    copy_term( (ExitVars,EntryVars, Cs), (ExitVars_aux,EntryVars_aux, Cs_aux) ),
    append(ExitVars_aux,EntryVars_aux,Vars_aux),
    numbervars( Vars_aux,0,Dim),
    to_ppl_dim(Dim, Cs_aux,Handle_Cs),
    ppl_one_affine_ranking_function_PR_C_Polyhedron(Handle_Cs,point(Rf)),
    from_numbervars_nu(EntryVars,(ExitVars_aux,Rf),(_,Sym_Rf)),
    dispose(Handle_Cs).

% Mesnard and Serebrenik method to obtain a polyhedra with all the linear ranking functions
nad_all_ranking_functions_MS(EntryVars,ExitVars,Cs,Rfs) :-
    copy_term( (ExitVars,EntryVars, Cs), (ExitVars_aux,EntryVars_aux, Cs_aux) ),
    append(ExitVars_aux,EntryVars_aux,Vars_aux),
    numbervars( Vars_aux,0,Dim),
    length(ExitVars,Dim2),
    to_ppl_dim(Dim, Cs_aux,Handle_Cs),
    ppl_all_affine_ranking_functions_MS_C_Polyhedron(Handle_Cs,Handle_Solution),
    ppl_Polyhedron_remove_higher_space_dimensions(Handle_Solution,Dim2),
    ppl_Polyhedron_get_generators(Handle_Solution, Gen),
    get_points(Gen,Points),
    from_numbervars_nu(EntryVars,(ExitVars_aux,Points),(_,Rfs)),
    dispose(Handle_Solution),
    dispose(Handle_Cs).

%Podelski and Rybalchenko method to obtain a polyhedra with all the linear ranking functions
nad_all_ranking_functions_PR(EntryVars,ExitVars,Cs,Rfs) :-
    copy_term( (ExitVars,EntryVars, Cs), (ExitVars_aux,EntryVars_aux, Cs_aux) ),
    append(ExitVars_aux,EntryVars_aux,Vars_aux),
    numbervars( Vars_aux,0,Dim),
    length(ExitVars,Dim2),
    to_ppl_dim(c,Dim, Cs_aux,Handle_Cs),
    ppl_all_affine_ranking_functions_PR_C_Polyhedron(Handle_Cs,Handle_Solution),
    ppl_Polyhedron_remove_higher_space_dimensions(Handle_Solution,Dim2),
    ppl_Polyhedron_get_generators(Handle_Solution, Gen),
    get_points(Gen,Points),
    from_numbervars_nu(EntryVars,(ExitVars_aux,Points),(_,Rfs)),
    dispose(Handle_Solution),
    dispose(Handle_Cs).

get_points([],[]).
get_points([point(X)|Xs],[X|Ps]):-!,
	get_points(Xs,Ps).
get_points([point(X,D)|Xs],[X/D|Ps]):-!,
	get_points(Xs,Ps).
get_points([_|Xs],Ps):-
	get_points(Xs,Ps).



get_generators(Vars,Cs,Gen_out) :-
    copy_term( (Vars, Cs), (Vars_aux, Cs_aux) ),
    numbervars( Vars_aux,0,Dim),
    to_ppl_dim(Dim, Cs_aux,Handle_Cs),
    ppl_Polyhedron_get_generators(Handle_Cs, Gen),
    from_numbervars_nu(Vars,(Vars_aux,Gen),(_,Gen_out)),
    dispose(Handle_Cs).

    
dispose(Handle) :- ppl_delete_Polyhedron(Handle).

from_ppl( Handle, _Dim, Vars, Elem) :-     
    ppl_Polyhedron_get_constraints(Handle,Ground_Cs),
    from_numbervars_nu(Vars, Ground_Cs, Elem).
    
from_ppl_minimized( Handle, _Dim, Vars, Elem) :-     
    ppl_Polyhedron_get_minimized_constraints(Handle,Ground_Cs),
    from_numbervars_nu(Vars, Ground_Cs, Elem).
    
to_ppl_dim(Dim , Elem, Handle ) :-
    ppl_new_C_Polyhedron_from_space_dimension(Dim, universe, Handle), 
    ppl_Polyhedron_add_constraints(Handle, Elem).