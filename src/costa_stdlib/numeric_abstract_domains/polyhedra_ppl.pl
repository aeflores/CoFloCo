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

:- module(polyhedra_ppl,[
    ppl_my_initialize/0,
    ppl_project/4,
    ppl_lub/7,
    ppl_glb/4,
    ppl_difference/4,
    ppl_list_lub/3,
    ppl_list_glb/3,
    ppl_h79_widen/6,
    ppl_entails/4,
    ppl_equivalent/4,
    ppl_consistent_constraints/2,
	ppl_solve/4,
    ppl_entailed_cone/6, % ( c, Cs, Vars, Mode, Params, Psi).
	ppl_minimize/4,
	ppl_maximize/4,
    ppl_pp_c_collapse/2, 
    ppl_normalize/3,
    ppl_ranking_function_MS/5,
    ppl_ranking_function_PR/5,
    ppl_all_ranking_functions_MS/5,
    ppl_all_ranking_functions_PR/5,
    get_generators/4
			 
]).

:- use_module(stdlib(numvars_util)).

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
 	  ppl_all_affine_ranking_functions_PR_C_Polyhedron/2
 ]).

:- use_module(stdlib(res_polyhedra),[lp_get_point/2]). 
:- use_module(stdlib(matrix_constraint)).

:- use_module(stdlib(list_utils),[length_lu/2,take_lu/3]).
:- use_module(stdlib(utils),[ut_length/2]). 

% ***IMPORTANT****
%
% SOME PROLOG DISTRIBUTIONS initialize PPL automatically when it's loaded, 
% but in other you have to call it explicitly.
%
ppl_my_initialize :- ppl_initialize.

/*
ppl_project(+PPLType,+Xs,+Cxs,-ProjectCxs): 
 * Xs is a list of variables, 
 * Cxs is a list of contraints,
 * Projectxs is the projection of the Constraints Cxs on the variables Cs
*/
ppl_project(Type,Vars, Elem,Proj_Elem) :-
    to_numbervars_nu( f(Vars,Elem), _, f(_,Elem_x), Dim),
    to_ppl_dim(Type, Dim, Elem_x, Handle),
    length(Vars,Proj_Dim),
    remove_higher_dimensions(Type , Handle, Proj_Dim),
    from_ppl(Type, Handle, Proj_Dim, Vars, Proj_Elem),
    dispose(Type,Handle).

remove_higher_dimensions(c , Handle, Dim) :- 
    ppl_Polyhedron_remove_higher_space_dimensions(Handle,Dim).
remove_higher_dimensions(o , Handle, Dim) :- 
    ppl_Octagonal_Shape_mpz_class_remove_higher_space_dimensions(Handle,Dim).
remove_higher_dimensions(nnc , Handle, Dim) :- 
    ppl_Polyhedron_remove_higher_space_dimensions(Handle,Dim).
remove_higher_dimensions(pp_c , Handle, Dim) :- 
    ppl_Pointset_Powerset_C_Polyhedron_remove_higher_space_dimensions(Handle, Dim).
    
/*
ppl_lub(+Type, +Xs, +Cxs, +Ys, +Cys, +Zs, +Czs) : 

 * Xs and Ys are list of variables of the same length, 
 * Cxs and Cys are lists of constraints of the variables of Xs and
   Ys repressively, 
 * Zs is a list of new fresh variables of the same length as Xs and Ys,
 * Czs is a list of constrains over Zs which represents the lub operation  
   of Cxs and Cys as elements of Type.
*/
ppl_lub(Type, Xs, Cxs, Ys, Cys, Zs, Czs) :-
    copy_term( f(Xs,Ys,Cxs,Cys),f(Vs_x,Vs_x,Cxs_x,Cys_x) ),
    numbervars([Vs_x],0,Dim),
    to_ppl_dim(Type, Dim, Cxs_x, Handle_x), 
    to_ppl_dim(Type, Dim, Cys_x, Handle_y), 
    lub_x(Type, Handle_x, Handle_y), 
    from_ppl(Type , Handle_x, Dim, Zs, Czs), 
    dispose(Type,Handle_x),
    dispose(Type,Handle_y).

lub_x( c, Handle_x, Handle_y) :- 
    ppl_Polyhedron_upper_bound_assign(Handle_x,Handle_y).
lub_x( o, Handle_x, Handle_y) :- 
    ppl_Octagonal_Shape_mpz_class_upper_bound_assign(Handle_x,Handle_y).

lub_x( nnc, Handle_x, Handle_y) :- 
    ppl_Polyhedron_upper_bound_assign(Handle_x,Handle_y).

lub_x( pp_c,Handle_x, Handle_y) :- 
    ppl_Pointset_Powerset_C_Polyhedron_upper_bound_assign(Handle_x, Handle_y).

ppl_lub2(Type, Elem_A, Elem_B, Lub) :-
    to_numbervars_nu( [Elem_A,Elem_B], _, [Elem_Ax, Elem_Bx], Dim), 
    to_ppl_dim(Type, Dim, Elem_Ax, Handle_A), 
    to_ppl_dim(Type, Dim, Elem_Bx, Handle_B), 
    lub_x(Type, Handle_A, Handle_B), 
    from_ppl(Type , Handle_A, Dim, _Vars, Lub), 
    dispose(Type,Handle_A),
    dispose(Type,Handle_B).

/*
ppl_glb(+Type, +Cxs, +Cys, -Glb) : 

 * Cxs and Cys are lists of constraints of the variables 
 * Glb is the Ppl object that represents the the greatest lower bound 
    of Cxs and Cys as elements of Type.
*/
ppl_glb(Type, Elem_A, Elem_B, Glb) :-
    to_numbervars_nu( (Elem_A, Elem_B), Vars, (Elem_Ax, Elem_Bx), Dim), 
    to_ppl_dim(Type, Dim, Elem_Ax, Handle_x), 
    to_ppl_dim(Type, Dim, Elem_Bx, Handle_y), 
    glb_x(Type, Handle_x, Handle_y), 
    from_ppl(Type , Handle_x, Dim, Vars, Glb), 
    dispose(Type,Handle_x),
    dispose(Type,Handle_y).

glb_x( c, Handle_x, Handle_y) :- 
    ppl_Polyhedron_intersection_assign(Handle_x,Handle_y).
glb_x( o, Handle_x, Handle_y) :- 
    ppl_Octagonal_Shape_mpz_class_intersection_assign(Handle_x,Handle_y).

glb_x( nnc, Handle_x, Handle_y) :- 
    ppl_Polyhedron_intersection_assign(Handle_x,Handle_y).

glb_x( pp_c,Handle_x, Handle_y) :- 
    ppl_Pointset_Powerset_C_Polyhedron_intersection_assign(Handle_x, Handle_y).



ppl_difference( Type, Elem_A, Elem_B, Diff) :- 
    to_numbervars_nu( (Elem_A, Elem_B), Vars, (Elem_Ax, Elem_Bx), Dim), 
    to_ppl_dim(Type, Dim, Elem_Ax, Handle_x), 
    to_ppl_dim(Type, Dim, Elem_Bx, Handle_y), 
    difference_x(Type, Handle_x, Handle_y), 
    from_ppl(Type , Handle_x, Dim, Vars, Diff), 
    dispose(Type,Handle_x),
    dispose(Type,Handle_y).
    
difference_x( c, Handle_x, Handle_y) :- 
    ppl_Polyhedron_difference_assign(Handle_x,Handle_y).

difference_x( nnc, Handle_x, Handle_y) :- 
    ppl_Polyhedron_difference_assign(Handle_x,Handle_y).

difference_x( pp_c,Handle_x, Handle_y) :- 
    ppl_Pointset_Powerset_C_Polyhedron_difference_assign(Handle_x, Handle_y).


/*
ppl_list_lub( Type, Elems, Lub_Elem) 


*/
ppl_list_lub( Type , Elems, Lub) :- 
    to_numbervars_nu( Elems, Vars, Elems_x, Dim), 
    ppl_empty_dim( Type, Dim, Handle), 
    list_lub_x( Elems_x, Type, Dim, Handle),
    from_ppl(Type, Handle, Dim, Vars, Lub), 
    dispose(Type, Handle).
    
list_lub_x( [], _Type, _Dim, _Handle ) . 
list_lub_x( [Elem|Elems],Type, Dim,  Handle) :-
    list_lub_xx( Elem, Type, Dim, Handle), 
    list_lub_x( Elems, Type, Dim, Handle).

list_lub_xx( Elem, Type, Dim, Handle) :- 
    to_ppl_dim(Type, Dim, Elem, Handle_x), 
    lub_x( Type, Handle, Handle_x), 
    dispose( Type, Handle_x). 


ppl_empty_dim( c , Dim , Handle) :- 
    ppl_new_C_Polyhedron_from_space_dimension(Dim, empty, Handle).
ppl_empty_dim( o , Dim , Handle) :- 
    ppl_new_Octagonal_Shape_mpz_class_from_space_dimension(Dim, empty, Handle). 

ppl_empty_dim( nnc , Dim , Handle) :- 
    ppl_new_NNC_Polyhedron_from_space_dimension(Dim, empty, Handle). 
    
ppl_empty_dim( pp_c , Dim , Handle) :- 
        ppl_new_Pointset_Powerset_C_Polyhedron_from_space_dimension(
        Dim, empty,Handle
    ). 


/*
ppl_list_glb( Type, Elems, Lub_Elem) 

*/
ppl_list_glb( Type , Elems, Glb) :- 
    to_numbervars_nu( Elems, Vars, Elems_x, Dim), 
    ppl_univ_dim( Type, Dim, Handle), 
    list_glb_x( Elems_x, Type, Dim, Handle),
    from_ppl(Type, Handle, Dim, Vars, Glb), 
    dispose(Type, Handle).
    
list_glb_x( [], _Type, _Dim, _Handle ). 
list_glb_x( [Elem|Elems], Type, Dim, Handle) :-
    list_glb_xx( Elem, Type, Dim, Handle), 
    list_glb_x(Elems, Type, Dim, Handle).

list_glb_xx( Elem, Type, Dim, Handle) :- 
    to_ppl_dim(Type, Dim, Elem, Handle_x), 
    glb_x( Type, Handle, Handle_x), 
    dispose( Type, Handle_x).
    
ppl_univ_dim( c , Dim , Handle) :- 
    ppl_new_C_Polyhedron_from_space_dimension(Dim, universe, Handle).
ppl_univ_dim( o , Dim , Handle) :- 
    ppl_new_Octagonal_Shape_mpz_class_from_space_dimension(Dim, universe, Handle). 

ppl_univ_dim( nnc , Dim , Handle) :- 
    ppl_new_NNC_Polyhedron_from_space_dimension(Dim, universe, Handle). 
    
ppl_univ_dim( pp_c , Dim , Handle) :- 
        ppl_new_Pointset_Powerset_C_Polyhedron_from_space_dimension(
        Dim, universe,Handle
    ). 


/*
ppl_h79_widen(+Type , +Vars,+Clist1,+Clist2,-WidenVars,-ClistWiden) : 
 * Clist1, Clist2 are lists of constraints on Vars such that Clist2>=Clist1, 
 * WidenVars  are fresh variables 
 * ClistWiden is the result of selecting the constraints from Clist1
    which are entailed by Clist2. ****Clist2>=Clist1***

This predicates was taken from the termination analyser of Cohavit Taboch 
and Mike Codish
*/
ppl_h79_widen(Type, Vars,Clist1,Clist2,WidenVars,ClistWiden) :-
    to_numbervars_nu([Vars,Clist1,Clist2],_,[_,Clist1_x,Clist2_x],Dim),
    to_ppl_dim(Type, Dim, Clist1_x, Handle_1),
    to_ppl_dim(Type, Dim, Clist2_x, Handle_2),
    widening_assign(Type, Handle_2, Handle_1),
    from_ppl(Type , Handle_2, Dim, WidenVars,ClistWiden), 
    dispose(Type,Handle_1),
    dispose(Type,Handle_2).

widening_assign(c, Handle_1, Handle_2) :- 
    ppl_Polyhedron_H79_widening_assign(Handle_1,Handle_2).
widening_assign(o, Handle_1, Handle_2) :- 
    ppl_Octagonal_Shape_mpz_class_BHMZ05_widening_assign(Handle_1,Handle_2). 

widening_assign(nnc, Handle_1, Handle_2) :- 
    ppl_Polyhedron_H79_widening_assign(Handle_1,Handle_2). 

widening_assign(pp_c, Handle1, Handle2) :- 
    ppl_Pointset_Powerset_C_Polyhedron_BHZ03_H79_H79_widening_assign(
        Handle1, Handle2
    ),
    ppl_Pointset_Powerset_C_Polyhedron_pairwise_reduce(Handle1).

/*
ppl_entails( +Type, +Vars, +Clist1, +Clist2):

Succeeds if and only if the polyhedron Clist1 entails the polyhedron Clist2.
*/
ppl_entails(Type,Vars,Clist1,Clist2) :-
    to_numbervars_nu(f(Vars,Clist1,Clist2),_, f(_,Clist1_x,Clist2_x),Dim), 
    to_ppl_dim(Type, Dim, Clist1_x, Handle_1), 
    to_ppl_dim(Type, Dim, Clist2_x, Handle_2), 
    ( contains_ppl(Type, Handle_2,Handle_1) 
        ->  R=entails
        ;   R=does_no_entail
    ),
    dispose(Type,Handle_1),
    dispose(Type,Handle_2),
    !,
    R= entails.

contains_ppl(c, Handle_1,Handle_2) :- 
    ppl_Polyhedron_contains_Polyhedron(Handle_1, Handle_2).
contains_ppl(o, Handle_1,Handle_2) :- 
   ppl_Octagonal_Shape_mpz_class_contains_Octagonal_Shape_mpz_class(Handle_1, Handle_2).

contains_ppl(nnc, Handle_1,Handle_2) :- 
    ppl_Polyhedron_contains_Polyhedron(Handle_1, Handle_2).

contains_ppl(pp_c, Handle_1,Handle_2) :- 
    ppl_Pointset_Powerset_C_Polyhedron_geometrically_covers_Pointset_Powerset_C_Polyhedron(
        Handle_1 , Handle_2
    ). 
%   

/*
*/
ppl_equivalent(Type,Vars,Clist1,Clist2) :-
    to_numbervars_nu( f(Vars,Clist1,Clist2), _, f(_,Clist1_x,Clist2_x), Dim),
    to_ppl_dim(Type, Dim, Clist1_x, Handle_1), 
    to_ppl_dim(Type, Dim, Clist2_x, Handle_2), 
    ( equivalent_ppl(Type, Handle_2,Handle_1) 
        ->  R=yes 
        ;   R=no 
    ),
    dispose(Type,Handle_1),
    dispose(Type,Handle_2),
    !,
    R= yes.

equivalent_ppl(c, Handle_1,Handle_2) :- 
    ppl_Polyhedron_equals_Polyhedron(Handle_1, Handle_2).
equivalent_ppl(o, Handle_1,Handle_2) :- 
    ppl_Octagonal_Shape_mpz_class_equals_Octagonal_Shape_mpz_class(Handle_1, Handle_2).

equivalent_ppl(nnc, Handle_1,Handle_2) :- 
    ppl_Polyhedron_equals_Polyhedron(Handle_1, Handle_2).

equivalent_ppl(pp_c, Handle_1,Handle_2) :- 
    ppl_Pointset_Powerset_C_Polyhedron_geometrically_equals_Pointset_Powerset_C_Polyhedron(
        Handle_1 , Handle_2
    ). 
%   

/*
ppl_consistent_constraints( + Type, + Cs):

Succeeds if and only if Cs are consistent
*/
ppl_consistent_constraints(Type,Cs) :-
    to_numbervars_nu( Cs, _Vars, Cs_aux, Dim), 
    to_ppl_dim(Type,Dim, Cs_aux,Handle_Cs),
    (is_empty_ppl(Type, Handle_Cs) -> R=empty ; R=not_empty),
    dispose(Type,Handle_Cs),
    !,
    R=not_empty.
    
is_empty_ppl(nnc, Handle) :- ppl_Polyhedron_is_empty(Handle).
is_empty_ppl(c  , Handle) :- ppl_Polyhedron_is_empty(Handle).
is_empty_ppl(o  , Handle) :- ppl_Octagonal_Shape_mpz_class_is_empty(Handle).
is_empty_ppl(pp_c, Handle):- ppl_Pointset_Powerset_C_Polyhedron_is_empty(Handle).



/*
  ppl_solve( + Type, + Cs, + Vs, - Vals) :-
 
*/
ppl_solve( c, Cs, Vs , Vals ) :-
    to_numbervars_nu( f(Vs,Cs), _Vars, f(Vs_x,Cs_x), _Dim),
    from_constraints_mrep( Cs_x, Vs_x, leq, MRep),
    lp_get_point( MRep, Vals_x),
    length_lu( Vs, D1),
    take_lu( D1, Vals_x,Vals).

/*
    ppl_entailed_cone( c, Cs, Vars, Mode, Params, Psi).
*/
ppl_entailed_cone( c, Cs, Vars, Mode, Params, Psi) :-
    constraints_entailed_cone( Cs, Vars, Mode, Params, Psi_x), 
    ppl_project( c, Params, Psi_x, Psi). 

/*
ppl_minimize(+Type,+Cs,+Vs):

Minimize the variables Vs in the context of Cs, it fails if it
cannot find a minimum for one of the variables. Also it REQUIRES
MINIMUM NOT INFIMUM. It binds Vs to the minimum values.

*/
ppl_minimize(Type,Cs,Vs,Ms) :-
	catch(ppl_minimize_aux(Type,Cs,Vs),min_vec(Ms_vec),Ms=Ms_vec).

ppl_minimize_aux(Type,Cs,Vs) :-
    numbervars([Vs,Cs],0,Dim),
    to_ppl_dim(Type, Dim, Cs, Handle), 
	minimize_vars(Type,Vs,Handle,Ms),
	dispose(Type,Handle), 
	throw(min_vec(Ms)).

minimize_vars(_Type,[], _Handle, []).
minimize_vars(Type,[V|Vs], Handle, [C|Cs]) :-
	!,
	minimize_vars(Type,V, Handle, C),
	minimize_vars(Type,Vs,Handle,Cs).

minimize_vars(Type,V, Handle, C) :- 
    ( Type = c ; Type = nnc), 
    ppl_Polyhedron_minimize(Handle, V, C1, C2, true), 
    ppl_Polyhedron_add_constraints(Handle, [C2*V=C1]), 
    C = C1/C2.

minimize_vars(pp_c,V, Handle, C) :- 
    ppl_Pointset_Powerset_C_Polyhedron_minimize(Handle, V, C1, C2, true), 
    ppl_Pointset_Powerset_C_Polyhedron_add_constraints(Handle, [C2*V=C1]), 
    C = C1/C2.

/*
ppl_maximize(+Type,+Cs,+Vs):

Maximize the variables Vs in the context of Cs, it fails if it
cannot find a minimum for one of the variables. Also it REQUIRES
MINIMUM NOT INFIMUM. It binds Vs to the minimum values.
*/
ppl_maximize(Type,Cs,Vs,Ms) :-
	catch(ppl_maximize_aux(Type,Cs,Vs),min_vec(Ms_vec),Ms=Ms_vec).

ppl_maximize_aux(Type,Cs,Vs) :-
    numbervars([Vs,Cs],0,Dim),
    to_ppl_dim(Type, Dim, Cs, Handle), 
	maximize_vars(Type,Vs,Handle,Ms),
    dispose(Type,Handle), 
	throw(min_vec(Ms)).

% TODO explore how to put it in foldr-form
maximize_vars(_Type,[], _Handle, []).
maximize_vars(Type,[V|Vs], Handle, [C|Cs]) :-
	!,
	maximize_vars(Type,V, Handle, C),
	maximize_vars(Type,Vs,Handle,Cs).

maximize_vars(Type,V, Handle, C) :-
    ( Type = c ; Type = nnc), 
	ppl_Polyhedron_maximize(Handle, V, C1, C2, true),
	ppl_Polyhedron_add_constraints(Handle,[C2*V=C1]),
	C = C1/C2.

maximize_vars(pp_c,V, Handle, C) :-
    ppl_Pointset_Powerset_C_Polyhedron_maximize(Handle, V, C1, C2, true),
    ppl_Pointset_Powerset_C_Polyhedron_add_constraints(Handle,[C2*V=C1]),
    C = C1/C2.


/*
to_ppl_dim ( type, + Dim + Constraints,  - Handle) ::

Handle is the handle of a PPL_Object of type Type that represents the 
Constraints, and has dimension Dim. 
*/
to_ppl_dim( c , Dim , Elem, Handle ) :-
    ppl_new_C_Polyhedron_from_space_dimension(Dim, universe, Handle), 
    ppl_Polyhedron_add_constraints(Handle, Elem).

to_ppl_dim( o , Dim , Elem, Handle2 ) :-
    ppl_new_C_Polyhedron_from_space_dimension(Dim, universe, Handle),
    ppl_Polyhedron_add_constraints(Handle, Elem),
    ppl_new_Octagonal_Shape_mpz_class_from_C_Polyhedron(Handle,Handle2),
    ppl_delete_Polyhedron(Handle).
    

to_ppl_dim( nnc , Dim , Elem, Handle ) :-
    ppl_new_NNC_Polyhedron_from_space_dimension(Dim, universe, Handle), 
    ppl_Polyhedron_add_constraints(Handle, Elem).

to_ppl_dim(pp_c, Dim, Elem,Handle) :- 
    ppl_new_Pointset_Powerset_C_Polyhedron_from_space_dimension(
        Dim, empty,Handle
    ),
    pp_c_to_ppl_dim_x(Elem, Dim, Handle). 

pp_c_to_ppl_dim_x([], _Dim, _Handle) :-!. 
pp_c_to_ppl_dim_x([ Disj | Disjs ],  Dim,  Handle) :-
    pp_c_to_ppl_dim_xx( Disj, Dim, Handle), 
    pp_c_to_ppl_dim_x(Disjs, Dim,Handle).

pp_c_to_ppl_dim_xx( Disj, Dim, Handle ) :- 
    ppl_new_C_Polyhedron_from_space_dimension(Dim, universe, DHandle),
    ppl_Polyhedron_add_constraints(DHandle, Disj), 
    ppl_Pointset_Powerset_C_Polyhedron_add_disjunct(Handle, DHandle).
%   ppl_delete_Pointset_Powerset_C_Polyhedron(DHandle). 


/*
from_ppl( + Type, + Handle, + Dim , + Vars, -Constraints)

Constraints is the constraint system that describes the PPL Object which 
is accessed thorugh Handle, of type Type, and by employing a certain 
set of Variables. 
*/

from_ppl_minimized( T, H, D, Vs, Cs) :-
    ut_length( Vs, D),
    from_ppl_x_minimized( T,H,D,Vs,Cs).

from_ppl_x_minimized(c, Handle, _Dim, Vars, Elem) :-     
    ppl_Polyhedron_get_minimized_constraints(Handle,Ground_Cs),
    from_numbervars_nu(Vars, Ground_Cs, Elem).


from_ppl( T, H, D, Vs, Cs) :-
    ut_length( Vs, D),
    from_ppl_x( T,H,D,Vs,Cs).

from_ppl_x(c, Handle, _Dim, Vars, Elem) :-     
    ppl_Polyhedron_get_constraints(Handle,Ground_Cs),
    from_numbervars_nu(Vars, Ground_Cs, Elem).

from_ppl_x(o, Handle, _Dim, Vars, Elem) :-     
    ppl_Octagonal_Shape_mpz_class_get_constraints(Handle,Ground_Cs),
    from_numbervars_nu(Vars, Ground_Cs, Elem).

from_ppl_x(nnc, Handle, _Dim, Vars, Elem) :-     
    ppl_Polyhedron_get_constraints(Handle,Ground_Cs),
    from_numbervars_nu(Vars, Ground_Cs, Elem).

from_ppl_x(pp_c, Handle, _Dim, Vars,  Elem ) :- 
    ppl_Pointset_Powerset_C_Polyhedron_size( Handle, Size), 
    ppl_Pointset_Powerset_C_Polyhedron_begin_iterator(Handle, Iter),
    pp_c_from_ppl_x( Size, Iter, Ground_Cs), 
    ppl_delete_Pointset_Powerset_C_Polyhedron_iterator(Iter),
    from_numbervars_nu(Vars, Ground_Cs, Elem).   

pp_c_from_ppl_x(0 , _Iter, [] ) :- !. 
pp_c_from_ppl_x(Size , Iter, [Disj |Disjs] ) :- 
    % implicit: Size > 0
    pp_c_from_ppl_xx( Iter, Disj), 
    ppl_Pointset_Powerset_C_Polyhedron_increment_iterator(Iter),
    S1 is Size -1 ,
    pp_c_from_ppl_x(S1,Iter, Disjs).

pp_c_from_ppl_xx( Iter, Disj) :- 
    ppl_Pointset_Powerset_C_Polyhedron_get_disjunct(Iter, Handle),
    ppl_Polyhedron_get_constraints(Handle,Disj).


/*
*/
ppl_pp_c_collapse(D_Cs, Cs) :-   
    to_numbervars_nu( D_Cs, Vars, Cs_x, Dim), 
    to_ppl_dim(pp_c,Dim, Cs_x,Handle),     
    ppl_new_C_Polyhedron_from_space_dimension(Dim, empty, NHandle), 
    collapse_x( Handle, NHandle), 
    ppl_delete_Pointset_Powerset_C_Polyhedron(Handle), 
    from_ppl(c, NHandle, Dim, Vars, Cs),
    ppl_delete_Polyhedron(NHandle).

collapse_x( Handle, NHandle) :-     
    ppl_Pointset_Powerset_C_Polyhedron_size( Handle, Size), 
    ppl_Pointset_Powerset_C_Polyhedron_begin_iterator(Handle, Iter),
    collapse_xx(Size,Iter,NHandle),    
    ppl_delete_Pointset_Powerset_C_Polyhedron_iterator(Iter). 

collapse_xx(0,_Iter,_Handle) :- !. 
collapse_xx(S,Iter,NHandle) :- 
    % Implicit: S > 0,
    ppl_Pointset_Powerset_C_Polyhedron_get_disjunct(Iter, Handle),
    ppl_Polyhedron_upper_bound_assign(NHandle, Handle),
    ppl_Pointset_Powerset_C_Polyhedron_increment_iterator(Iter),
    S1 is S -1 ,
    collapse_xx(S1,Iter, NHandle).


/*
ppl_nomalize ( Type, Cs, Normal_Cs) is det. 

gives a normalized representation of Cs, which means that it eliminates all 
its redundancies. 
*/
ppl_normalize( Type , Cs, NCs) :- 
    to_numbervars_nu( Cs, Vars, Cs_x, Dim),
    to_ppl_dim(Type,Dim, Cs_x,Handle),
    from_ppl_minimized(Type, Handle, Dim, Vars, NCs). 

/*
dispose( Type, Handle) 

Instructs the PPL to dispose of the Handle, releasing its memory. 
*/
dispose(c, Handle) :- ppl_delete_Polyhedron(Handle).
dispose(o, Handle) :- ppl_delete_Octagonal_Shape_mpz_class(Handle). 
dispose(nnc, Handle) :- ppl_delete_Polyhedron(Handle). 
dispose(pp_c, Handle) :- ppl_delete_Pointset_Powerset_C_Polyhedron(Handle). 


%interface of the parma polyhedra library of automatic linear ranking function generation


% Mesnard and Serebrenik method to obtain a single ranking function
ppl_ranking_function_MS(Type,EntryVars,ExitVars,Cs,Sym_Rf) :-
    copy_term( (ExitVars,EntryVars, Cs), (ExitVars_aux,EntryVars_aux, Cs_aux) ),
    append(ExitVars_aux,EntryVars_aux,Vars_aux),
    numbervars( Vars_aux,0,Dim),
    to_ppl_dim(c,Dim, Cs_aux,Handle_Cs),
    ppl_one_affine_ranking_function_MS_C_Polyhedron(Handle_Cs,point(Rf)),
    from_numbervars_nu(EntryVars,(ExitVars_aux,Rf),(_,Sym_Rf)),
    dispose(Type,Handle_Cs).

%Podelski and Rybalchenko method to obtain a single ranking function
ppl_ranking_function_PR(Type,EntryVars,ExitVars,Cs,Sym_Rf) :-
    copy_term( (ExitVars,EntryVars, Cs), (ExitVars_aux,EntryVars_aux, Cs_aux) ),
    append(ExitVars_aux,EntryVars_aux,Vars_aux),
    numbervars( Vars_aux,0,Dim),
    to_ppl_dim(c,Dim, Cs_aux,Handle_Cs),
    ppl_one_affine_ranking_function_PR_C_Polyhedron(Handle_Cs,point(Rf)),
    from_numbervars_nu(EntryVars,(ExitVars_aux,Rf),(_,Sym_Rf)),
    dispose(Type,Handle_Cs).

% Mesnard and Serebrenik method to obtain a polyhedra with all the linear ranking functions
ppl_all_ranking_functions_MS(Type,EntryVars,ExitVars,Cs,Rfs) :-
    copy_term( (ExitVars,EntryVars, Cs), (ExitVars_aux,EntryVars_aux, Cs_aux) ),
    append(ExitVars_aux,EntryVars_aux,Vars_aux),
    numbervars( Vars_aux,0,Dim),
    length(ExitVars,Dim2),
    to_ppl_dim(c,Dim, Cs_aux,Handle_Cs),
    ppl_all_affine_ranking_functions_MS_C_Polyhedron(Handle_Cs,Handle_Solution),
    ppl_Polyhedron_remove_higher_space_dimensions(Handle_Solution,Dim2),
    ppl_Polyhedron_get_generators(Handle_Solution, Gen),
    get_points(Gen,Points),
    from_numbervars_nu(EntryVars,(ExitVars_aux,Points),(_,Rfs)),
    dispose(Type,Handle_Solution),
    dispose(Type,Handle_Cs).

%Podelski and Rybalchenko method to obtain a polyhedra with all the linear ranking functions
ppl_all_ranking_functions_PR(Type,EntryVars,ExitVars,Cs,Rfs) :-
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
    dispose(Type,Handle_Solution),
    dispose(Type,Handle_Cs).

get_points([],[]).
get_points([point(X)|Xs],[X|Ps]):-!,
	get_points(Xs,Ps).
get_points([point(X,D)|Xs],[X/D|Ps]):-!,
	get_points(Xs,Ps).
get_points([_|Xs],Ps):-
	get_points(Xs,Ps).

%todo
%ppl_termination_test_MS_C_Polyhedron
%ppl_termination_test_PR_C_Polyhedron

get_generators(Type,Vars,Cs,Gen_out) :-
    copy_term( (Vars, Cs), (Vars_aux, Cs_aux) ),
    numbervars( Vars_aux,0,Dim),
    to_ppl_dim(Type,Dim, Cs_aux,Handle_Cs),
    ppl_Polyhedron_get_generators(Handle_Cs, Gen),
    from_numbervars_nu(Vars,(Vars_aux,Gen),(_,Gen_out)),
    dispose(Type,Handle_Cs).

 %   get_points(Gen,Points),
 %   from_numbervars_nu(EntryVars,(ExitVars_aux,Points),(_,Rfs)),
 
%    dispose(Type,Handle_Cs).