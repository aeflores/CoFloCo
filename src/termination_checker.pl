/**  <module>  termination_checker

This module tries to prove termination of the different chains using the previously inferred
ranking functions.
The termination arguments are saved in phase_termination_argument/4 so they can be consulted afterwards.


Specific "data types" of this module:
  * termination_argument:
      * 'trivial' : for non-iterative phases
      * list((list(equation_id),linear_expression/'no')):
        represent a lexicographic ranking function 
        where each ranking function has a list of equation ids that
        are guaranteed to terminate. if the list contains an element (List,no),
        that means that the equations in List might execute forever.

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



:- module(termination_checker,[init_termination/0,
		       prove_termination/2,
		       termination_argument/4,
		       phase_termination_argument/5]).

:- use_module(ranking_functions,[ranking_function/4,
				 partial_ranking_function/7]).
:- use_module('refinement/chains',[chain/3]).
:- use_module('IO/params',[get_param/2]).
:- use_module('IO/output',[print_phase_termination_argument/4]).
:- use_module('utils/polyhedra_optimizations',[nad_normalize_polyhedron/2]).
:- use_module('utils/cofloco_utils',[bagof_no_fail/3]).
:- use_module(stdlib(set_list)).



%! phase_termination_argument(Head:term,Chain:chain,Phase:phase,YesNo:flag,Term_argument:termination_argument)
% store whether a phase in a chain is guaranteed to terminate and its termination argument
% a termination argument of a phase can be:
%  * trivial: if the phase is not iterative
%  * a lexicographical ranking function: the lexicographical ranking function is represented as a list of pairs.
%    where each pair has a list of loops and a ranking function. Those loops are constrained by the ranking function.
%    The list of pairs is ordered.
%  * no: if we could not prove termination of the phase
:- dynamic  phase_termination_argument/5.

%! termination_argument(Head:term,Chain:chain,YesNo:flag,Term_argument:list(termination_argument))
% store whether a chain is guaranteed to terminate and the termination argument for each of its phases
:- dynamic  termination_argument/4.

%! init_termination
%clear the termination arguments database
init_termination:-
	retractall(termination_argument(_,_,_,_)),
	retractall(phase_termination_argument(_,_,_,_,_)).





%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! prove_termination(+Head,+RefCnt:int) is det
% try to prove termination of all the chains in the SCC of Head
prove_termination(Head,RefCnt):-
	chain(Head,RefCnt,Chain),
	
	maplist(prove_phase_termination(Head,Chain),Chain,Termination_argument),
	save_termination_argument(Head,Chain,Termination_argument),
	%for now, the chain does not affect in anything (we prove termination of a generic phase in any chain)
	maplist(save_phase_termination_argument(Head,_),Chain,Termination_argument),
	fail.
prove_termination(_,_).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! prove_phase_termination(+Head,+Chain:chain,+Phase:phase,+Term_argument:termination_argument) is det
% try to prove termination of Phase in Chain in SCC Head:
%  * if the phase is not iterative, return trivial
%  * if the termination has already been proved, consult the stored argument
%  * if the phase has a ranking function, return it
%  * otherwise, try to find a lexicographic ranking function
prove_chain_termination([],_Head,[]).

prove_phase_termination(_Head,_Chain,Phase,trivial):-
	number(Phase),!.
		
prove_phase_termination(Head,Chain,Phase,Part_term_arg):-
	phase_termination_argument(Head,Chain,Phase,_,Part_term_arg),!.
	
prove_phase_termination(Head,Chain,Phase,[(Phase,rf(Rf))]):-
	ranking_function(Head,Chain,Phase,Rf),!.
	
prove_phase_termination(Head,Chain,Phase,Phase_rf):-
	bagof_no_fail(NDeps-val(Loops,Rf,Deps_set),Deps^E1^(
			partial_ranking_function(Head,Chain,Phase,Loops,Rf,Deps,E1),
			from_list_sl(Deps,Deps_set),
			length(Deps_set,NDeps)	       
			),Deps_structure),
	%order ranking function by number of dependencies
	keysort(Deps_structure,Sorted_structure),
	find_lexicographic_proof_1(Sorted_structure,Phase,[],Phase_rf).

%if there are no loops left, terminate
find_lexicographic_proof_1(_Sorted_structure,[],Term_arg,Term_arg):-!.
%if there are loops left but not ranking functions, return the remaining loops with a 'no' flag
find_lexicographic_proof_1([],Rem_lg,Rf_accum,[(Rem_lg,no)|Rf_accum]):-!.
% if there is ranking function with 0 dependencies, remove the loops involved
% and decrease the dependencies accordingly
find_lexicographic_proof_1([0-val(Loops,Rf,_Dep_set)|Deps],Rem_lg,Rf_accum,Term_arg):-!,
	difference_sl(Rem_lg,Loops,Rem_lg1),
	prune_loops_structure(Deps,Loops,Deps1),
	prune_deps_structure(Deps1,Loops,Deps2),
	find_lexicographic_proof_1(Deps2,Rem_lg1,[(Loops,rf(Rf))|Rf_accum],Term_arg).

%if the next ranking function has dependencies:
% * try to reorder the ranking functions and continue
% * if even so all ranking functions have dependencies, return 'no'
find_lexicographic_proof_1([N-val(Loop,Rf,Dep_set)|Deps],Rem_lg,Rf_accum,Term_arg):-
	N>0,
	keysort([N-val(Loop,Rf,Dep_set)|Deps],[N2-val(Loop2,Rf2,Dep_set2)|Deps2]),
	(N2=0->
	 find_lexicographic_proof_1([N2-val(Loop2,Rf2,Dep_set2)|Deps2],Rem_lg,Rf_accum,Term_arg)
	;
	 Term_arg=[(Rem_lg,no)]
	).

prune_loops_structure([],_,[]).
prune_loops_structure([N-val(Loops1,Rf,Dep_set)|Deps],Loops2,Deps1):-
	difference_sl(Loops1,Loops2,Rest),
	prune_loops_structure(Deps,Loops2,Deps_aux),
	(Rest\=[]->
	    Deps1=[N-val(Loops1,Rf,Dep_set)|Deps_aux]
	    ;
	    Deps1=Deps_aux
	    ).
prune_deps_structure([],_,[]).
prune_deps_structure([_-val(Loops,Rf,Dep_set)|Deps],Loops2,[N2-val(Loops,Rf,Dep_set2)|Desp1]):-
	difference_sl(Dep_set,Loops2,Dep_set2),
	length(Dep_set2,N2),
	prune_deps_structure(Deps,Loops2,Desp1).

	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

save_termination_argument(Head,Chain,Term_argument):-
	member([(_,no)|_],Term_argument),!,
	assertz(termination_argument(Head,Chain,no,Term_argument)).
save_termination_argument(Head,Chain,Term_argument):-
	assertz(termination_argument(Head,Chain,yes,Term_argument)).

save_phase_termination_argument(Head,Chain,Phase,_Term_argument):-
	phase_termination_argument(Head,Chain,Phase,_,_),!.
	
save_phase_termination_argument(Head,Chain,Phase,Term_argument):-
        [(_,no)|_]=Term_argument,!,
        assertz(phase_termination_argument(Head,Chain,Phase,no,Term_argument)),
        print_phase_termination_argument(Head,Phase,Term_argument,no).
	
save_phase_termination_argument(Head,Chain,Phase,Term_argument):-
	assertz(phase_termination_argument(Head,Chain,Phase,yes,Term_argument)),
	print_phase_termination_argument(Head,Phase,Term_argument,yes).
