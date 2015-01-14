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

:- module(numvars_util,[ from_numbervars_nu/3, to_numbervars_nu/4 ]). 

:- use_module(stdlib(list_utils), [ divide_in_chunks_lu/3 ]).
:- use_module(stdlib(parsing_writing),[   write_lists_map/3 ]).
    
/*
from_numbervars_nu( 
    + Vars: list<var>, 
    + NV_Term:term, 
    - V_Term:term
) is det.

Translates the groung term NV_Term to another term, by substituting every 
subexpression '$VAR(N)' with the variable at Vars[N], where N is a natural. 

*/
from_numbervars_nu(Vars, Ground_Term , Term) :- 
    create_vars_table(Vars,Dic),
    from_numvars_x(Dic, Ground_Term , Term).

from_numvars_x(_Dic, Exp, Exp) :- 
    var(Exp), 
    !.

from_numvars_x(_Dic, Exp, Exp) :- 
    atomic(Exp), 
    !.

from_numvars_x(Dic,Exp, Var ) :- 
    compound(Exp), 
    Exp = '$VAR'(Num), 
    !,
    vars_table_lookup(Dic,Num,Var).

from_numvars_x( Dic, [Exp|Exps], [NExp|NExps]) :-
    !,
    from_numvars_x(Dic, Exp, NExp),
    from_numvars_x(Dic, Exps, NExps). 

from_numvars_x( Dic, Exp, NExp) :- 
    compound(Exp),
    Exp =.. [F | Args],
    from_numvars_x(Dic, Args, NArgs),
    NExp =.. [F|NArgs].

create_vars_table(Vars,Dic) :-
    divide_in_chunks_lu(255,Vars,Chunks),
    write_lists_map(g,Chunks, CVars),
    Dic =.. [f|CVars].

vars_table_lookup(Dic,N,V) :-
    P1 is (N // 255)+1,
    P2 is (N+1)-(P1-1)*255,
    arg(P1,Dic,SubDic),
    arg(P2,SubDic,V),
    !.    

/*
to_numbervars_nu( 
    + Term:term ,  - Vars:list<var> ,  - GTerm:term ,  - Dim:integer
  ) is det. 
    
  * Vars is the list of variables in Term
  * GTerm is a copy of Term such that for each i, the variable Vars[i] in
  Term is replaced with $VAR(i)  in GTerm. 

Postconditions: 
 * Vars is the set of variables of Term, appearing in preorden
  (depth-first, left-to-right), 
 * GTerm is a ground term, in which Vars[i] is replaced with $VAR(i),
 * Dim is the length of the list Vars. 

*/
to_numbervars_nu( Term , Vars, GTerm , Dim) :- 
    my_term_variables( Term, Vars),
    copy_term( f(Vars, Term), f(Vs_x, GTerm) ),
    numbervars( Vs_x, 0, Dim).

:- use_module(stdlib(utils),[ut_varset_withoutorder/2]).
:- use_module(stdlib(list_utils),[nub_lu/2]).
my_term_variables( Term, Vars) :-
	term_variables(Term,Vars).
    %ut_varset_withoutorder(Term, VBag),
    %nub_lu( VBag, Vars).

    
