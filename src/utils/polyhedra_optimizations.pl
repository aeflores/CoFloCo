/** <module> polyhedra_optimizations

 This module implements some predicates to optimize
 polyhedral operations. These optimizations are based on separating the
 sets of constraints into independent subsets and operating with each of the subsets
 independently.
  This is specially effective for operations that involve a 
 big number of variables as the operations can have exponential complexity
 with that respect.
 
 For some operations, we just want to obtain the subset of constraints and variables
 that are related to a given set of variables.
 For that, we use slice_relevant_constraints_and_vars/5.
 


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



:- module(polyhedra_optimizations,[
			slice_relevant_constraints/4,
		    slice_relevant_constraints_and_vars/5,
		    nad_consistent_constraints_group/2,
		    nad_consistent_constraints_group_aux/1,
		    nad_entails_aux/3,
		    nad_normalize_polyhedron/2,
		    nad_project_group/3,
		    nad_is_bottom/1,
		    group_relevant_vars/4
	]).
	
:- use_module(cofloco_utils,[normalize_constraint/2,constraint_to_coeffs_rep/2]).
:- use_module(stdlib(numeric_abstract_domains),[nad_normalize/2,nad_project/3,nad_entails/3,nad_consistent_constraints/1,nad_lub/6,nad_list_lub/2]).
:- use_module(stdlib(set_list)).	
:- use_module(stdlib(utils),[ut_flat_list/2,ut_var_member/2]).

%! nad_is_bottom(+Cs:polyhedron) is semidet
% succeeds if Cs is inconsistent (unsatisfiable) using cartesian decomposition incrementally.
nad_is_bottom([X=Y]):-X==0,Y==1,!.
nad_is_bottom(Cs):-
	\+nad_consistent_constraints_group_aux(Cs).
	
%! nad_entails_aux(+Vars:list(var),+Cs:polyhedron,+Cons:list(linear_constraint)) is semidet
% succeeds if Cs (with variables Vars) => (implies) Cons.
nad_entails_aux(Vars,Cs,Cons):-
	maplist(normalize_constraint,Cons,Cons_norm),
	term_variables(Cons_norm,Relevant_vars),
	slice_relevant_constraints_and_vars(Relevant_vars,Vars,Cs,Selected_vars,Selected_Cs),
    nad_entails(Selected_vars,Selected_Cs,Cons_norm).


nad_normalize_polyhedron(Cs,Cs4):-
	nad_normalize(Cs,Cs2),
	maplist(normalize_constraint,Cs2,Cs3),
	from_list_sl(Cs3,Cs4).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! nad_consistent_constraints_group_aux(+Cs:polyhedron) is semidet
% succeeds if Cs is consistent (satisfiable) using cartesian decomposition incrementally.	
nad_consistent_constraints_group_aux(Cs):-
	term_variables(Cs,Vars),
	nad_consistent_constraints_group(Vars,Cs).

%! nad_consistent_constraints_group(+Vars:list(var),+Cs:polyhedron) is semidet
% succeeds if Cs is consistent with variables Vars (satisfiable) using cartesian decomposition incrementally.
nad_consistent_constraints_group(Vars,Cs):-
	from_list_sl(Vars,Vars_set),
	partition(ground,Cs,Ground_Cs,Cs_rest),
	nad_consistent_constraints(Ground_Cs),
	from_list_sl(Cs_rest,Cs_set),
	nad_consistent_constraints_group_1(Vars_set,Cs_set).
	
	
%! nad_consistent_constraints_group_1(Vars:list_set(var),Cs:list_set(linear_constraint)) is semidet
% succeeds if the part of Cs related to Vars is consistent (satisfiable).
nad_consistent_constraints_group_1([],_Cs).
    
nad_consistent_constraints_group_1([V|Vars],Cs):-
    slice_relevant_constraints_and_vars_1([V],[V|Vars],Cs,Selected_vars_set,Selected_Cs_set),
    difference_sl(Vars,Selected_vars_set,Rem_vars),
    difference_sl(Cs,Selected_Cs_set,Rem_Cs),
    nad_consistent_constraints(Selected_Cs_set),
    nad_consistent_constraints_group_1(Rem_vars,Rem_Cs).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%    

%! nad_project_group(+Vars:list(var),+Cs:polyhedron,-Cs2:polyhedron) is det
% project Cs onto Vars using cartesian decomposition (group_relevant_vars/4)
nad_project_group(Vars,Cs,Cs4):-
	copy_term((Vars,Cs),(Vars2,Cs2)),
	partition(equality,Cs2,_Equalities,Rest),
	term_variables(Vars2,Vars3),
	(Rest=[]->
	   Cs3=[]
	   ;
	nad_project_group1(Vars3,Rest,Cs3)
	),
	equate(Vars,Vars2,[],[],Cs3,Cs4).
	
	
nad_project_group1(Vars,Cs,Cs2):-
	from_list_sl(Vars,Vars_set),
	from_list_sl(Cs,Cs_set),
	group_relevant_vars(Vars_set,Cs_set,Groups,Rest),
	(\+nad_consistent_constraints(Rest)->
	  Cs2=[0=1]
	  ;
	maplist(project_group,Groups,Projected),
	ut_flat_list(Projected,Cs1),
	(ut_var_member(0=1,Cs1)->
	    Cs2=[0=1]
	    ;
	    Cs2=Cs1
	    )
	    ).

	
project_group((Vars,Cs),Cs2):-
	nad_project(Vars,Cs,Cs2).


equate([],[],_,Unify_list,Accum,Accum):-
	maplist(unify_elem,Unify_list).
equate([V|Vs],[V2|Vs2],Present,Unify_list,Accum,Cs):-
	(contains_sl(Present,V2)->
	   equate(Vs,Vs2,Present,Unify_list,[V2=V|Accum],Cs)
	   ;
	   insert_sl(Present,V2,Present2),
	   equate(Vs,Vs2,Present2,[V=V2|Unify_list],Accum,Cs)
	   ).
	
unify_elem(A=A).
equality(Constr):-
    constraint_to_coeffs_rep(Constr, coeff_rep([-1*A,1*A],=,0)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! group_relevant_vars(+Vars:set_list(var),+Cs:polyhedron,-Groups:list(set_list(var),polyhedron),-Rest:polyhedron) is det
% given a set of variables Vars and a set of constraints Cs, obtain a list of independent polyhedra and their corresponding variables.
% That is, express Cs as a cartesian product of smaller polyhedra.
%
% Rest contains constraints that have no variables (only constants). If Cs is inconsistent it might contain 1=0.
group_relevant_vars([],Rest,[],Rest).
    
group_relevant_vars([V|Vars],Cs,[(Selected_vars,Selected_Cs)|Groups],Rest):-
    slice_relevant_constraints_and_vars_1([V],[V|Vars],Cs,Selected_vars,Selected_Cs),
    difference_sl(Vars,Selected_vars,Rem_vars),
    difference_sl(Cs,Selected_Cs,Rem_Cs),
    group_relevant_vars(Rem_vars,Rem_Cs,Groups,Rest).	
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    
%! slice_relevant_constraints_and_vars(Relevant_vars_ini:list(var),Vars:list(var),Cs:list(linear_expression),Selected_vars:list_set(var),Selected_Cs:list_set(linear_constraint)) is det
% given a list of initial variables Relevant_vars_ini collect all the constraints and variables
% in Vars and Cs related to the initial variables.
%
% return the variables and the constraints in set format: Selected_vars and Selected_Cs
slice_relevant_constraints_and_vars(Relevant_vars_ini,Vars,Cs,Selected_vars,Selected_Cs):-
	from_list_sl(Cs,Cs_set),
	from_list_sl(Relevant_vars_ini,Relevant_vars_ini_set),
	from_list_sl(Vars,Vars_set),
	slice_relevant_constraints_and_vars_1(Relevant_vars_ini_set,Vars_set,Cs_set,Selected_vars,Selected_Cs).
	

%! slice_relevant_constraints_and_vars_1(Relevant_vars_ini:list_set(var),Vars:list_set(var),Cs:list_set(linear_expression),Selected_vars:list_set(var),Selected_Cs:list_set(linear_constraint)) is det
% given a set of initial variables Relevant_vars_ini collect all the constraints and variables
% in Vars and Cs related to the initial variables.
% This predicate expects that Vars and Cs are ordered lists (list_set).
%
% return the variables and the constraints in set format: Selected_vars and Selected_Cs 
slice_relevant_constraints_and_vars_1(Relevant_vars_ini,Vars_set,Cs_set,Selected_vars,Selected_Cs_set):-
	slice_relevant_constraints(Relevant_vars_ini,Cs_set,Relevant_vars,Selected_Cs),
	intersection_sl(Relevant_vars,Vars_set,Selected_vars),
	from_list_sl(Selected_Cs,Selected_Cs_set).

%! slice_relevant_constraints(+Relevant_vars_ini:list_set(var),+Cs:list_set(linear_expression),-Selected_vars:list_set(var),-Selected_Cs_set:list_set(linear_constraint)) is det
% given a set of initial variables Relevant_vars_ini collect all the constraints in Cs and variables
% related to the initial variables.
% This predicate expects that Vars and Cs are ordered lists (list_set).
%
% return the variables and the constraints in set format: Selected_vars and Selected_Cs_set
slice_relevant_constraints(Relevant_vars_ini,Cs,Selected_vars,Selected_Cs_set):-
	maplist(annotate_constraint,Cs,Cs_annotated),
	slice_relevant_constraints_1(Cs_annotated,Relevant_vars_ini,[],Selected_vars,Selected_Cs),
	from_list_sl(Selected_Cs,Selected_Cs_set).

%! annotate_constraint(+C:linear_constraint,-Annotated_C:(list_set(var),linear_constraint)) is det
% annotate a constraint with the set of variables that it contains
annotate_constraint(C,(Vars_set,C)):-
	term_variables(C,Vars),
	from_list_sl(Vars,Vars_set).

%! slice_relevant_constraints_1(+Cs:list((list_set(var),linear_constraint)),+Vars_set:list_set(var),+Accum:list(linear_constraint),-Selected_vars:list_set(var),-Selected_Cs:list(linear_constraints)) is det
% collect all the constraints of Cs that are related to the variables in Vars_set.
% Vars_set serves as an accumulator for variables and Accum for constraints.
slice_relevant_constraints_1([],Selected_vars,Selected_Cs,Selected_vars,Selected_Cs):-!.
slice_relevant_constraints_1(Cs,Vars_set,Accum,Selected_vars,Selected_Cs):-
	filter_constraints(Cs,[],Vars_set,Accum,Cs_1,Vars_set_1,Accum_1),
	length(Vars_set,N),
	length(Vars_set_1,N1),
	% is it a fixpoint?
	(N1>N ->
	% make another pass on Cs_1 with the new collected variables Vars_set1
	  slice_relevant_constraints_1(Cs_1,Vars_set_1,Accum_1,Selected_vars,Selected_Cs)
	;
	% we reached a fixpoint (we did not add any new constraint) and we are done
	 Selected_Cs=Accum_1,
	 Selected_vars=Vars_set_1
	).
%! filter_constraints(+Cs:list((list_set(var),linear_constraint)),+Accum_rem:list((list_set(var),linear_constraint)),+Vars:list_set(var),+Accum_selected:list(linear_constraint),-Cs_rem:list((list_set(var),linear_constraint)),-Vars_out:set_list(var),-Cs_selected:list(linear_constraint)) is det
% make a pass on Cs, collect constraints related to Vars and put them in Cs_selected.
% Cs_rem has the rest of the constraints annotated. The set of variables can grow during the pass.
% The final set of variables is Vars_out.
%
% for each constraint C  in Cs, check if it contains vars of Vars.
% if it does, we add C to the Accum_selected and add the variables of C to Vars.
% otherwise, we add C to Accum_rem.
filter_constraints([],Cs_rem,Vars_out,Cs_selected,Cs_rem,Vars_out,Cs_selected).
filter_constraints([([],C)|Cs],Accum_rem,Vars,Accum_selected,Cs_rem,Vars_out,Cs_selected):-!,
	filter_constraints(Cs,Accum_rem,Vars,[C|Accum_selected],Cs_rem,Vars_out,Cs_selected).

filter_constraints([(Vs,C)|Cs],Accum_rem,Vars,Accum_selected,Cs_rem,Vars_out,Cs_selected):-
	intersection_sl(Vs,Vars,[]),!,
	filter_constraints(Cs,[(Vs,C)|Accum_rem],Vars,Accum_selected,Cs_rem,Vars_out,Cs_selected).

filter_constraints([(Vs,C)|Cs],Accum_rem,Vars,Accum_selected,Cs_rem,Vars_out,Cs_selected):-
	union_sl(Vs,Vars,Vars1),
	filter_constraints(Cs,Accum_rem,Vars1,[C|Accum_selected],Cs_rem,Vars_out,Cs_selected).
	
	
	
%FIXME it seems to work well for one case but not for invariant generation	
%this can loose precision!!	
/*
nad_lubs_group(Cs_list,Cs_lub):-
	maplist(from_list_sl,Cs_list,Cs_set_list),
	unions_sl(Cs_set_list,Cs_total),
	term_variables(Cs_total,Vars),
	from_list_sl(Vars,Vars_set),
	group_relevant_vars_1(Vars_set,Cs_total,Groups),
	maplist(get_2nd_element,Groups,Cs_groups),
	maplist(intersection_aux(Cs_groups),Cs_set_list,Cs_factored_list),
		nad_lubs_aux(Cs_factored_list,Lub_factored),	
	ut_flat_list(Lub_factored,Cs_lub).
	
intersection_aux(Groups,Cs_set,Cs_factored):-
	maplist(intersection_sl(Cs_set),Groups,Cs_factored).
	
nad_lubs_aux([[]|_],[]):-!.
nad_lubs_aux(Lists,[Factor|Factors]):-
	 maplist(head_rest,Lists,Heads,Rests),
	 (member([],Heads)->
	    Factor=[];
	 nad_list_lub(Heads,Factor)
	 ),	
	 nad_lubs_aux(Rests,Factors).
	 
	 
head_rest([X|Y],X,Y).
get_2nd_element((_,X),X).	 
*/	 	
	
	