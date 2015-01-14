/*
    Copyright (C) 2009  E.Albert, P.Arenas, S.Genaim, G.Puebla, and D.Zanardini
                        https://costa.ls.fi.upm.es

    This program is free software: you can redistribute it and/or modify it 
    under the terms of the GNU General Public License as published by the Free
        Software Foundation, either version 3 of the License, or (at your option) 
        any later version.

    This program is distributed in the hope that it will be useful, but WITHOUT 
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or 
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

:- module(vars_dictionary,[
    empty_vd/1,
    put_vd/4,
    put_list_vd/4,
    var_of_vd/3,
    join_vd/3,
    collapse_vd/1, 
    key_of_vd/3,
    clear_unified_vd/2
]).

/** <module> 
A vars_dictionary (VD) is a mapping of the elements of a certain type A to 
variables. It is useful when big data structures are to be handled atomically 
but need to be compared and handled several times. 
Handling and comparing the variables becomes, in that case, an easier option. 

type vars_dictionary<A> = map<A,var>. 

We shorten vars_dictionary<A> as vdict<A>.

@author Diego Alonso
@license GPL
*/

:- use_module(list_map).
:- use_module(maybe).
:- use_module(stdlib(parsing_writing),[write_foldr1/3]).
:- use_module(pair_list,[unzip/3,zip_with/4, remove_second_pl/3]). 

/*
empty_vd( ? VDict:vdict<A> ) is det. 

VDict is an empty Vars Dictionary. 
*/
empty_vd([]).


/*
put_vd( + VDict : vdict<A> )  is det.
*/
% When adding a variable, we don't change anything. 
put_vd(VDict, Elem, Elem, VDict) :-
    var(Elem), 
    !. 
put_vd(VDict, Elem, Var, NVDict) :-
    % Implicit by cut: \+ var(Elem) 
    open_cursor_lm(VDict,Elem,MVal,Cursor),
    eval_maybe(MVal,Var,Var),
    close_cursor_lm(Cursor, [(Elem,Var)], NVDict).

/*
put_list_vd( + VDict:vdict<A>,  + Elems: list<A>, 
    - Vars:list<var>, - NVD:vdict<A>
) is det. 

*/
put_list_vd(VDict,[],[],VDict) :- !.
put_list_vd(VDict,[Elem|Elems],[Var|Vars],NVDict) :-
    put_list_vd(VDict,Elems,Vars,NVD1),
    put_vd(NVD1, Elem, Var, NVDict).

/*
var_of_vd
*/
var_of_vd( Dict, Elem, Var) :- lookup_lm(Dict, Elem, Var). 

/*
key_of_vd
*/
key_of_vd( Dict, Var, Key) :- key_of_lm( Dict, Var, Key). 

/*
join_vd( + ADict: vdict<A> , + BDict:vdict<A>, - JDict:vdict<A> ) is det.

Joins two variable dictionaries: unile joining list_maps, that works by 
strict term equality joining a variable dictionary works by unification. 


*/
join_vd( [] , [], []). 
join_vd( [] , [B|Db], [B|Db]). 
join_vd( [A|Da] , [], [A|Da]). 
join_vd( [ RecA | ADict] , [RecB | BDict] , [JRec|JDict]) :- 
    RecA = (AElem, _AVar), 
    RecB = (BElem, _BVar), 
    compare( Comp, AElem, BElem), 
    join_x( Comp,  [ RecA | ADict] , ADict_x, [RecB | BDict], BDict_x, JRec), 
    join_vd( ADict_x, BDict_x, JDict).

join_x( <, [RecA|ADict], ADict, BDict, BDict, RecA). 
join_x( =, [RecA|ADict], ADict, [RecB | BDict], BDict, RecA) :- RecA = RecB. 
join_x( >, ADict, ADict, [RecB | BDict], BDict, RecB). 

/*
clear_unified_vd( + Dict:vdict<A>, - NDict : vdict<A> ) is det.

Detects all the records that contain the same variable as value and removes 
all of them except the first one. 
*/
clear_unified_vd( [] , []). 
clear_unified_vd( [ (Nat,Var) | Dict] , [ (Nat,Var) | NDict] ) :- 
    remove_second_pl( Dict, Var, Dict1), 
    clear_unified_vd( Dict1, NDict). 

/*
collapse_vd( + VDict:vdict<A>) is det. 

Collapses the vars dictionary, which means that it unifies each expression with 
the variable which it's mapped to.
This predicate "unnaturalizes" the variables dictionary. After calling it, the 
var dictionary is no longer a var dictionary, but a sorted pairs of list 
"(A,A)". This, of course, is an identity map. 
*/
collapse_vd([]). 
collapse_vd([P|Ps]) :- 
    unzip([P|Ps], As,Vars), 
    zip_with( '=', As, Vars, Unifs), 
    write_foldr1(Unifs,',',Goal),
    call(Goal).
