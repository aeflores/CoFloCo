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

:- module(relational,[
    is_relational/1,
    reverse_relational/2, 
    is_strict/1,
    to_increase_relational/2,
    to_decrease_relational/2,
    strict_nonstrict_relational/2
]).

/** <module> General predicates for handling Relational operators. 

Those relational operators can be described with this grammar: 
relational ::=  '='              equals
            |   '=<'             less than or equal
            |   '>='             greater than or equal
            |   '<'              strictly less than
            |   '>'              strictly greater than

@author Diego Alonso
@license GPL
*/

/*
is_relational( + Atom:atom) is semidet.

True if Atom is one of the relational operators. 
*/
is_relational( < ).
is_relational( =<).
is_relational( = ).
is_relational( >=).
is_relational( > ).

/*
reverse_relational( + Direct:relational , - Reverse:relational) is det.

Reverse is the reverse relational of Direct. That is to say, for each 
operator D gives the operator R such that, for two elements A,B, 
D(A,B) if and only if R(B,A).
*/
reverse_relational( <  , >  ).
reverse_relational( =< , >= ).
reverse_relational( =  , =  ).
reverse_relational( >= , =< ).
reverse_relational( >  , <  ).

/*
to_increase_relational( + Rel:relational , - Inc_Rel : relational ) is det.
*/
to_increase_relational( < , <  ).
to_increase_relational( =<, =< ).
to_increase_relational( = , =  ).
to_increase_relational( >=, =< ).
to_increase_relational( > , <  ).

/*
to_decrease_relational( + Rel:relational , - Inc_Rel : relational ) is det.
*/
to_decrease_relational( < , >  ).
to_decrease_relational( =<, >= ).
to_decrease_relational( = , =  ).
to_decrease_relational( >=, >= ).
to_decrease_relational( > , >  ).

/*
is_strict( + Oper:relational) is semidet.

True if Oper is an strict, non-reflexive, relational operator.
*/
is_strict(<).
is_strict(>).


strict_nonstrict_relational( <, =< ).
strict_nonstrict_relational( >, >= ).
