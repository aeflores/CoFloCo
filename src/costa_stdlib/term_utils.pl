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

/** <module> Utilities for manipulating terms, extending the basic predicates
provided by the iso prolog to lists of terms.

@author Diego Alonso
@license GPL
*/

:- module(term_utils,[
    arg_path/3,
    univ_terms/2,
    functor_to_vars/4,
    functor_to_vars_exclude/5,
    filter_vars/2,
    purge_vars/2,
    filter_functors/3,
    take_functors/3,
    purge_functors/3,
    search_functor/3, 
    take_functors/3,
    group_functor/2,
    span_functors/4, 
    abstract_functors/5,
    open_at_functor/5,
    functor_index/3, 
    functor_indices/3,
    functor_index_term/3,
    functor_indices_terms/3, 
    set_arg/4,
    set_args/4,
    replace_arg/5,
    remove_arg/3,
    remove_args/3,
    replace_args/5,
    terms_get_args/3,
    terms_set_args/4,
    terms_replace_args/5,
    terms_remove_args/3
]).

/** <module>

@author Diego Alonso
@license GPL
*/
:- use_module(stdlib(vars_dictionary)). 
:- use_module( stdlib(list_utils), [contains_lu/2,set_lu/4,set_many_lu/4,
    get_replace_lu/5,get_replace_many_lu/5, quit_many_lu/3,quit_lu/3]).

/*
arg_path( + Path:list<int>, +Term, -Value) is det. 
*/
arg_path([], Term, Term).
arg_path([Arg|Args], Term, Value) :-
    arg(Arg, Term, Branch),
    arg_path(Args, Branch, Value).

/*
setarg_path ( Path:list<int>, +Term, +Value) is det. 
*/
%setarg_path([] , _Term, _Value).
%setarg_path([Arg], Term, Value) :- 
%    !, 
%    setarg(Arg, Term, Value). 
%
%setarg_path([Arg|Args], Term, Value) :-
%    arg(Arg, Term, Branch),
%    setarg_path(Args, Branch, Value).

/*
terms_funtors( + Terms, - Functors) is det.


*/
terms_functors( [], []).
terms_functors( [Term|Terms], [Func|Funcs]) :- 
    functor( Term, Func, _Arity), 
    terms_functors( Terms, Funcs). 

/*
univ_terms
*/
univ_terms( [], []).
univ_terms( [Term | Terms] , [Univ|Univs]) :-
    Term =.. Univ,
    univ_terms(Terms, Univs).

/*
functor_to_vars( + Functor, + Term, - NTerm, - Table:vars_dictionary<>) 

It runs through a Term and builds a new NTerm by replacing each subterm which 
uses the Functor by a Variable, always employing the same Variable for two 
occurrences of syntactically equal subterms.

@param Table maps each term build with functor to the Variable in NTerm.

The predicate always operate on the most external subterm with Functor


*/
functor_to_vars( Func, Term, NTerm, Dict) :- 
    functor_to_vars_exclude( Func, [], Term, NTerm, Dict). 

/*
functor_to_vars_exclude( Func, Excluded, Term, NTerm, Dict)
*/
functor_to_vars_exclude( Func, Excl, Term, NTerm, Dict) :- 
    functor_to_vars_exclude_x( Func, Excl, Term, NTerm, [], Dict). 
    
functor_to_vars_exclude_x( _Func, _Excl, Var, Var, Dict, Dict) :- 
    var(Var), 
    !.
functor_to_vars_exclude_x( Func, _Excl, Term, Var, Dict, NDict) :- 
    Term =.. [ F | _Args], 
    Func == F, 
    !, 
    put_vd( Dict, Term, Var, NDict).
functor_to_vars_exclude_x( _Func, Excl, Term, Term, Dict, Dict) :- 
    Term =.. [ F | _Args], 
    contains_lu( Excl, F), 
    !.
functor_to_vars_exclude_x( Func, Excl, Term, NTerm, Dict, NDict) :-
    Term =.. [ F | Args], 
    % Implicit by cut: Func \== F, 
    !, 
    functor_to_vars_exclude_xx( Args, NArgs, Func, Excl, Dict, NDict), 
    NTerm =.. [F | NArgs].

functor_to_vars_exclude_xx(  [], [], _Func, _Excl,Dict, Dict). 
functor_to_vars_exclude_xx( [Arg|Args], [NArg|NArgs], Func, Excl, Dict, NDict) :-
    functor_to_vars_exclude_x( Func, Excl, Arg, NArg, Dict, Dict1),
    functor_to_vars_exclude_xx( Args, NArgs, Func, Excl, Dict1, NDict).

/*
filter_vars( + Terms: list<any>, -Vars:list<var>) is det.

Vars is the list of elements in Terms that are free variables.

filter_vars = filter is_var
*/
filter_vars( [],[]).
filter_vars( [Term|Terms],Vars) :- 
    filter_vars_x( Term, Vars0, Vars), 
    filter_vars( Terms, Vars0).

filter_vars_x( Term, Vars_x, Vars ) :- 
    var(Term)
    ->  Vars= [Term|Vars_x]
    ;   Vars = Vars_x .

/*
purge_vars( + Terms, - NTerms).
*/
purge_vars( [],[]).
purge_vars( [Term|Terms],NTerms) :- 
    purge_vars_x( Term, Terms0, NTerms), 
    purge_vars( Terms, Terms0).

purge_vars_x( Term, NTerms_x, NTerms ) :- 
    var( Term )
    ->  NTerms = NTerms_x 
    ;   NTerms = [Term|NTerms_x].

/*
filter_functors( + Terms, + Functors, - NTerms) is det.
*/
filter_functors( [], _Funcs, []).
filter_functors( [Term|Terms], Funcs, NTerms) :-
    filter_functors_x( Term, Funcs, NTerms0, NTerms),
    filter_functors( Terms, Funcs, NTerms0).

filter_functors_x( Term, Funcs, NTerms_x, NTerms ) :-
    (   nonvar(Term),
        Term =.. [ Func | _Args],
        contains_lu( Funcs, Func )
    )
    ->  NTerms = [ Term | NTerms_x ]
    ;   NTerms = NTerms_x.

/*
purge_functors( + Terms, + Functors, - NTerms) is det. 
*/
purge_functors( [], _Funcs, []).
purge_functors( [Term|Terms], Funcs, NTerms) :- 
    purge_functors_x( Term, Funcs, NTerms0, NTerms),
    purge_functors( Terms, Funcs, NTerms0).

purge_functors_x( Term, Funcs, NTerms_x, NTerms ) :- 
    (   nonvar(Term),
        Term =.. [ Func | _Args],
        contains_lu( Funcs, Func ) 
    ) 
    ->  NTerms = NTerms_x
    ;   NTerms = [Term|NTerms_x]. 

/*
partition_functors( + Terms, + Funcs, - In_Terms, - Out_Terms)

Partitions the list Terms in two lists: 
 - In_Terms contains those terms which functor is in Funcs.
 - Out_Terms contains the rest. 

*/
partition_functors( [], _Funcs,  [], []).
partition_functors( [Term|Terms], Funcs, Ins, Outs) :- 
    partition_x( Term, Funcs, Ins_x, Ins, Outs_x, Outs), 
    partition_functors( Terms, Funcs, Ins_x, Outs_x). 
    
partition_x( Term, Funcs, Ins_x, Ins, Outs_x, Outs) :- 
    nonvar( Term ), 
    Term =.. [Func|_Args], 
    contains_lu( Funcs, Func)
    ->  Ins = [Term|Ins_x], Outs = Outs_x
    ;   Ins = Ins_x , Outs = [Term  | Outs_x]. 

/*
take_functors( Terms, Funcs, Prefix ) 
*/
take_functors( [], _Funcs, [] ).
take_functors( [Term|Terms], Funcs, NTerms  ) :- 
    nonvar(Term), 
    Term =.. [ Func| _Args ],  
    contains_lu( Funcs, Func) 
    ->  NTerms = [Term|NTerms_x] , 
        take_functors( Terms, Funcs, NTerms_x)
    ;   NTerms = []. 


/*
search_functor( Terms , Functor, Term) is semidet.
*/
search_functor( [Term|_Terms] , Func, Term) :- 
    nonvar(Term), 
    Term =.. [Func | _Args], 
    !. 
search_functor( [_Term|Terms] , Func, Term) :- 
    search_functor( Terms, Func, Term). 


/*
group_functor( + Terms:list<compound>, - Groups: list<list<compound>>) is det.

*/
group_functor( [], []).
group_functor( [Term|Terms], [ [Term|Pref] | Groups] ) :- 
    Term =.. [Func|_],
    span_functors( Terms, [Func], Pref, Suff ),
    group_functor( Suff, Groups ).

/*
span_functors( + Terms:list<compound>, + Functors, - Prefix, - Suffix).
*/
span_functors( [], _Funcs, [], []).
span_functors( [Term|Terms], Funcs, Pref, Suff) :- 
    Term =.. [Fun |_Args],
    contains_lu( Funcs, Fun)
    ->  Pref = [Term|Pref_x], 
        span_functors( Terms, Funcs, Pref_x, Suff)
    ;   Pref = [] , 
        Suff = [Term|Terms].

/*
abstract_terms( 
    + Terms:list<nonvar>, + Functors, 
    - NTerms: list , - Vars: list<var>, - Found:list<nonvar>
) 

All the terms in Terms that are a compound of one of the functor are 
substituted by a variable in NTerms, 
Vars is that list of variables sorted and Terms are the chosen 

Precondition : te
*/
abstract_functors( [], _Functors, [], [], []). 
abstract_functors( [Term|Terms], Functors, [NTerm|NTerms], Vars, Found) :- 
    abs_functors_x( Term, Functors, NTerm, Vars_x, Vars, Found_x, Found), 
    abstract_functors( Terms, Functors, NTerms, Vars_x, Found_x).

abs_functors_x( Term, Funcs, Var, Vars, NVars, Founds, NFounds) :-
    functor( Term, F, _),
    contains_lu( Funcs, F),
    !,
    NVars = [Var|Vars],
    NFounds = [Term|Founds].
abs_functors_x( Term, _Funcs, Term, Vars, Vars, Founds, Founds ).


/*
open_at_functor( + Terms, + Functor, - Prefix, - TailVar, - Tail).
*/
open_at_functor( [], _Functor, Tail, Tail, [] ).
open_at_functor( [Term|Terms], Functor, Tail, Tail, NTerms ) :-
    nonvar(Term),
    functor( Term, Functor, _),
    !,
    NTerms = [Term|Terms].
open_at_functor( [Term|Terms], Functor, [Term|Prefix], TailVar, Tail ) :-
    open_at_functor( Terms, Functor, Prefix, TailVar, Tail).

/*
functor_index( + Terms, + Functor, - Index ) is nondet.
*/
functor_index( Terms, Functor, Index) :- 
    functor_index_x( Terms, Functor, 1, Index). 

functor_index_x( [Term|_Terms], Functor, Index, Index ) :- 
    nonvar(Term), 
    functor( Term, Functor, _).
functor_index_x( [_Term|Terms], Functor, Index, NIndex ) :- 
    Index_1 is Index + 1, 
    functor_index_x( Terms, Functor, Index_1, NIndex ).

/*
functor_indices( Terms, Functor, Index ) 
*/
functor_indices( Terms, Functor, Indices ) :- 
    functor_indices_x( Terms, Functor, 1, Indices ).

functor_indices_x( [], _Functor, _Indices, [] ).
functor_indices_x( [Term|Terms], Functor, Index, Indices ) :- 
    functor_indices_xx( Term, Functor, Index, Indices_x, Indices), 
    Index_1 is Index + 1, 
    functor_indices_x( Terms, Functor, Index_1, Indices_x ).

functor_indices_xx( Term, Functor, Index, Indices, [Index|Indices]) :- 
    nonvar(Term), 
    functor(Term, Functor, _), 
    !. 
functor_indices_xx( _Term, _Functor, _Index, Indices, Indices).

/*

*/
functor_index_term( Terms, Functor, TIx ) :- 
    functor_index_term_x( Terms, Functor, 1, TIx ). 

functor_index_term_x( [Term|_Terms], Functor, Index, (Index,Term) ) :- 
    nonvar( Term ),
    functor( Term, Functor, _).
functor_index_term_x( [_Term|Terms], Functor, Index, TIx ) :- 
    Index_1 is Index + 1, 
    functor_index_term_x( Terms, Functor, Index_1, TIx ).

/*
*/
functor_indices_terms( Terms, Functor, TIces ) :- 
    functor_indices_terms_x( Terms, Functor, 1, TIces). 
    
functor_indices_terms_x( [], _Functor, _Index, [] ).
functor_indices_terms_x( [Term|Terms], Functor, Index, TIces ) :- 
    functor_indices_terms_xx( Term, Functor, Index, TIces_x, TIces), 
    Index_1 is Index + 1, 
    functor_indices_terms_x( Terms, Functor, Index_1, TIces_x ).

functor_indices_terms_xx( Term, Func, Ix, TIces, [(Ix,Term)|TIces]) :- 
    nonvar(Term), 
    functor(Term, Func, _), 
    !. 
functor_indices_terms_xx( _Term, _Functor, _Index, TIces, TIces).


/*
set_arg( + Term, + Num: integer, + NArg, - NTerm) 

*/
set_arg( Term, Num, NArg, NTerm) :- 
    nonvar(Term), 
    Term =.. [ Func | Args], 
    ( Num = 0
    ->  nonvar(NArg), 
        NTerm =.. [ NArg | Args] 
    ;   set_lu( Args, Num, NArg, NArgs), 
        NTerm =.. [ Func | NArgs] 
    ).

/*
set_args( + Term,  + Nums: list<integer>, + NArgs, - NTerm ) is det.
*/
set_args( Term, Nums, NArgs, NTerm) :- 
    nonvar(Term), 
    Term =.. [ Func | Args], 
    set_many_lu( Args, Nums, NArgs, NArgs_x), 
    NTerm =.. [ Func | NArgs_x].

/*
replace_arg( + Term, + Num:integer, + NArg, - OArg, - NTerm) 
*/
replace_arg( Term, Num, NArg, OArg, NTerm) :- 
    nonvar(Term), 
    Term =.. [ Func | Args], 
    ( Num = 0 
    ->  OArg = Func, 
    	nonvar(NArg), 
        NTerm =.. [ NArg | Args] 
    ;   get_replace_lu( Args, Num, NArg, OArg, NArgs), 
        NTerm =.. [ Func | NArgs] 
    ).

/*
replace_args( + Term, + Nums, + NArgs, - OArgs, - NTerm) is det.

*/
replace_args( Term, Nums, NArgs, OArgs, NTerm) :- 
    nonvar(Term), 
    Term =.. [ Func | Args], 
    get_replace_many_lu( Args, Nums, NArgs, OArgs, NTArgs), 
    NTerm =.. [ Func | NTArgs].

/*
remove_arg( Term, Num, NTerm)
*/
remove_arg( Term, Num, NTerm) :- 
    Term =.. [ Func | Args], 
    quit_lu( Args, Num, NArgs), 
    NTerm =.. [ Func | NArgs].

remove_args( Term, Nums, NTerm ) :- 
    Term =.. [ Func | Args], 
    quit_many_lu( Args, Nums, NArgs ), 
    NTerm =.. [ Func | NArgs].

/*
terms_get_args( + Terms, + Arg:integer, - Vals) is det. 

For each index i, Vals[i] is the Arg-th argument of the term Terms[i].
If there is a term in Terms with less than Arg arguments, then the predicate
will raise an exception.

Examples: 
 * terms_get_args( [], 1, Vals)          ?       Vals = [].
 * terms_get_args( [f(a),f(b)], 1, Vals) ?       Vals = [a,b].

*/
terms_get_args( [], _Arg, []).
terms_get_args( [Term|Terms], Arg, [Val|Vals]) :-
    arg( Arg, Term, Val),
    terms_get_args( Terms, Arg, Vals).

/*
terms_set_args( Terms, Num, NArgs, NTerms). 
*/
terms_set_args( [], _Num, [], []). 
terms_set_args( [Term|Terms], Num, [NArg|NArgs], [NTerm|NTerms]) :- 
    set_arg( Term, Num, NArg, NTerm), 
    terms_set_args( Terms, Num, NArgs, NTerms). 

/*
terms_replace_args( 
    + Term, + Num, + NArgs, -OArgs, -NTerms
) is det.

*/
terms_replace_args( [], _Num, [], [], [] ).
terms_replace_args( 
    [Term|Terms], Num, [NArg|NArgs], [OArg|OArgs], [NTerm|NTerms] ) :- 
        replace_arg( Term, Num, NArg, OArg, NTerm),
        terms_replace_args( Terms, Num, NArgs, OArgs, NTerms).

/*
terms_remove_args( + Terms, + Num, - NTerms)

*/
terms_remove_args( [], _Num, [] ).
terms_remove_args( [Term|Terms], Num, [NTerm|NTerms] ) :-
    remove_arg( Term, Num, NTerm ),
    terms_remove_args( Terms, Num, NTerms ).

