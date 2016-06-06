

%%
%% c_polyhedra_ppl
%%
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

:- use_module(stdlib(polyhedra_ppl)).
:- use_module(stdlib(linear_constraint_system),[
    parse_lcs/2,
    write_natural_lcs/2
]). 

nad_available_domain(c_polyhedra_ppl).

nad_initialize_aux(c_polyhedra_ppl) :-	ppl_my_initialize.

nad_true_aux(c_polyhedra_ppl,Cs) :-
    Cs=[].

nad_false_aux(c_polyhedra_ppl,Cs) :-
	Cs=[0=1].

nad_import_aux(c_polyhedra_ppl,Cs, Import_Cs) :- 
    nonvar(Cs),
    parse_lcs(Cs, LCS),
    write_natural_lcs(LCS, Import_Cs).
    
nad_export_aux(c_polyhedra_ppl,Cs, Export_Cs) :- 
    parse_lcs(Cs, LCS),
    write_natural_lcs(LCS, Export_Cs).

nad_normalize_aux(c_polyhedra_ppl,Cs,Cs_normal) :-
	ppl_normalize(c,Cs,Cs_normal).

nad_project_aux(c_polyhedra_ppl,Vs,Cs,Projected_Cs) :-
	ppl_project(c,Vs,Cs,Projected_Cs).

nad_consistent_constraints_aux(c_polyhedra_ppl,Cs) :-
	ppl_consistent_constraints(c,Cs).

nad_entails_aux(c_polyhedra_ppl,Vs,Cs_1,Cs_2) :-
	ppl_entails(c,Vs,Cs_1,Cs_2).

nad_equivalent_aux(c_polyhedra_ppl,Vs,Cs_1,Cs_2) :-
    ppl_equivalent(c,Vs,Cs_1,Cs_2).

nad_lub_aux(c_polyhedra_ppl,Vs_1,Cs_1,Vs_2,Cs_2,Vs_3,Lub) :-
	ppl_lub(c,Vs_1,Cs_1,Vs_2,Cs_2,Vs_3,Lub).

nad_glb_aux(c_polyhedra_ppl, A, B,Glb) :-
    ppl_glb(c, A , B, Glb).

nad_difference_aux( c_polyhedra_ppl, A, B, Diff) :- 
    ppl_difference( c, A, B, Diff).


nad_list_lub_aux(c_polyhedra_ppl,Elems,Lub) :-
    ppl_list_lub(c,Elems, Lub).

nad_list_glb_aux(c_polyhedra_ppl,Elems, Glb) :-
    ppl_list_glb(c,Elems, Glb).

nad_widen_aux(c_polyhedra_ppl,Vs_1,Cs_1,Cs_2,Vs_3,Cs_3) :-
	ppl_h79_widen(c,Vs_1,Cs_1,Cs_2,Vs_3,Cs_3).

nad_minimize_aux(c_polyhedra_ppl,Cs,Vs,Ms) :-
	ppl_minimize(c,Cs,Vs,Ms).

nad_maximize_aux(c_polyhedra_ppl,Cs,Vs,Ms) :-
	ppl_maximize(c,Cs,Vs,Ms).

nad_solve_aux( c_polyhedra_ppl, Cs, Vs, Ms) :-
    ppl_solve( c, Cs, Vs, Ms).

nad_write_aux( c_polyhedra_ppl, Cs, WCs) :- 
    parse_lcs( Cs, Lcs), 
    write_natural_lcs(Lcs, WCs). 
    
nad_disjuncts_aux(  c_polyhedra_ppl, Cs, [Cs]).


nad_all_ranking_functions_PR_aux(c_polyhedra_ppl,EntryVars,ExitVars,Cs,Rfs):-
	ppl_all_ranking_functions_PR(c,EntryVars,ExitVars,Cs,Rfs).
nad_all_ranking_functions_MS_aux(c_polyhedra_ppl,EntryVars,ExitVars,Cs,Rfs):-
	ppl_all_ranking_functions_MS(c,EntryVars,ExitVars,Cs,Rfs).