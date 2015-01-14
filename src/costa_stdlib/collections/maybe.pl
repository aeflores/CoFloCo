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

/** <module> Elements of the type Maybe, that can represent either a value 
or no value.

The value is implemented with a list:
 * Null is the empty list
 * Just a as a singleton list of a 
singleton list.

type maybe<T> = list<T>

@author Diego Alonso
@license GPL
*/


:- module(maybe,[
    null_maybe/1,
    just_maybe/2,
    eval_maybe/3,
    cat_maybes/2
]).

:- use_module(list_utils,[ concat_lu/2 ]).

/*
null_maybe ( -Maybe:maybe<_> ) is det. 
null_maybe ( +Maybe:maybe<_> ) is semidet. 

Maybe contains no value of any type. 
*/
null_maybe( [] ).

/*
just_maybe( +Value:A , -Maybe:maybe<A>) is det. 
just_maybe( -Value:A , +Maybe:maybe<A>) is det. 
just_maybe( +Value:A , +Maybe:maybe<A>) is semidet. 

*/
just_maybe(Value, [Value] ).

/*
eval_maybe( + Maybe:maybe<A>, +Default:A , - Value:A) is det. 

Value is: 
 * Default if Maybe is Null. 
 * Val if Maybe is Just Val. 
 
 */
eval_maybe( [],    Def_Val,Def_Val).
eval_maybe( [Val],_Def_Val,Val).

/*
cat_maybes( +Maybes:list<maybe<A>>, -Values:list<A>) is det. 

This predicate takes a list of Maybes and returns a list with all the 
values that are inside a Just.
*/
cat_maybes(Maybes,Values) :- concat_lu(Maybes,Values). 
