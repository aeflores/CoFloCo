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

:- module(minimal_feedback_set,[compute_mfbs_shamir/3]).

/** <module> Algorithm that computes the minimal feedback set of a reducible 
graph in linear time. 

This algorithm was published by Adi Shamir in his paper 
"A Linear Time Algorithm for Finding Minimum Cutsets in Reducible Graphs",
published in the SIAM Journal of Computing in 1979.

The algorithm performs a depth first search on Graph and annotates each vertex
with the ordinal number in which it was visited (dfs_num) and a label.
This label is conveniently updated depending on the values of the vertex's 
successors, 
When the vertex is exhausted, the final values of dfs_num and label are used to 
determine if it's a feedback vertex, and also to detect if Graph is reducible.

@author 
@license GPL
*/

:- use_module(stdlib(list_utils),[contains_lu/2]).

:- dynamic dfs_num/2, label/2, edge/2, markedge/2.

/* compute_mfbs_shamir( 
    + Graph : list<V-V>, + Root : V, - Set : list<V> 
) is semidet.

True if Graph is a reducible, false if Graph is non-reducible.

@param Graph The directed Graph, represented as a list of edges Src-Targ
@param Root A Vertex employed as a root for starting the depth first search.
@param Set  If the predicate succeeds, a minimal feedback vertex set of Graph.
*/
compute_mfbs_shamir( Graph, Root, Set ) :-
    clear_db,
    store_graph( Graph ),
    catch(
        fbs_2( Root, [], 1, Set ),
        _,
        fail
    ),
    !.

/*
fbs_2( + Top:V, + Stack:list<V>, + Count:integer, - Set:list<V>)
Visits the vertex Top, pushed it into the Stack and
Top is an unvisited edge.
*/
fbs_2( Top, Stack, Count, Set ) :-
    dfs_visit( Top, Count ),
    NCount is Count + 1,
    fbs_3( [Top|Stack], NCount, Set ).

/* 
fbs_3( + Stack : list<V>, + Count : integer, - Set : list<V> ) is det.

Depth first search loop: takes the top vertex and looks to each outgoing edge.
When the vertex has no more fresh outgoing edges it performs the final process.
*/
fbs_3( [], _Count, [] ).
fbs_3( [Top|Stack], Count, Set ) :-
    ( edge( Top, Vert ), \+ markedge( Top, Vert) ) 
    ->  assertz( markedge(Top,Vert) ),
        fbs_4( Top, Vert, Stack, Count, Set )
    ;   fbs_7( Top, Set_x, Set ),
        fbs_8( Stack, Top ),
        fbs_3( Stack, Count, Set_x ).

/*
fbs_4( 
    + Top:V, + Vert:V, + Stack:list<V>, + Count:integer, - Set:list<V> 
) is det.
*/
fbs_4( Top, Vert, Stack, Count, Set ) :-
    visited( Vert )
    ->  fbs_5( Top, Vert, Stack ),
        fbs_3( [Top|Stack], Count, Set )
    ;   fbs_2( Vert, [Top|Stack], Count, Set ).

/*
fbs_5( + Top:V, + Vert:V, + Stack:list<V> ) is det.

*/
fbs_5( Top, Vert, Stack ) :-
    backwards_edge( Top, Vert, [Top|Stack] )
    ->  backwards_label( Top, Vert )
    ;   dag_label( Top, Vert ).

/*
fbs_7( + Vert:V, Set_x, Set ) is det.
For the vertex Vert without unused outgoing edges, it compares its depth-first
search number (n) and its label (l):
 * n > l Vert is not a feedback vertex.
 * n = l Vert is a feedback vertex.
 * n < l the Graph is non-reducible and Shamir's algorithm can't be used.
*/
fbs_7( Vert, Set_x, Set ) :-
    dfs_num( Vert, Nv ),
    label( Vert, Lv ),
    ( Nv > Lv   ->  Set =        Set_x
    ; Nv = Lv   ->  Set = [Vert|Set_x],
                     set_label( Vert, 0 )
    ; /*Nv < Lv */   throw(nonreducible)
    ).

/*
fbs_8( + Stack:list<V>, + Vert:V ) is det.

Updates the label of the top vertex of Stack, if any, through the edge to Vert. 
*/
fbs_8( [], _Vert).
fbs_8( [Top|_Stack], Vert ) :-
    dag_label( Top, Vert ).

/*
clear_db is det.
*/
clear_db :- 
    retractall( markedge(_MSrc,_MTarg) ),
    retractall( edge(_Src,_Targ) ),
    retractall( dfs_num( _NVert, _Num) ),
    retractall( label( _LVert, _Label) ).

/*
store_graph( + Graph:list<V-V> ) is det.
*/
store_graph( [] ).
store_graph( [Src-Targ|Edges] ) :-
    assertz( edge(Src,Targ) ),
    store_graph( Edges ).

/*
set_label( + Vert:V, + NLab:integer) is det.
*/
set_label( Vert , NLab ) :-
    retract( label( Vert,_Prev ) ),
    assertz( label( Vert, NLab ) ).

/*
dfs_visit( + Vert:V, + Count:integer ) is det.
*/
dfs_visit( Vert, Count ) :-
    assertz( dfs_num( Vert, Count) ),
    assertz( label( Vert, 0) ).

/*
visited( + Vert:V ) is semidet.
*/
visited( Vert ) :- dfs_num( Vert , _Num ).

/*
backwards_edge( + Src:V , + Targ:V, + Stack:list<V> ) is semidet.

True if Src-Targ is a backwards edge, i.e. if Targ is in Stack.

 * Fast-fail: backwards_edge( Src, Targ) -> n[Src] >= n[Targ]
 * If Graph is strongly connected, then
    backwards_edge( Src, Targ) <-> n[Src] >= n[Targ]
*/
backwards_edge( Src, Targ, Stack ) :-
    dfs_num( Src,  Sn ),
    dfs_num( Targ, Tn ),
    Sn >= Tn,
    contains_lu( Stack, Targ ).

/*
dag_label( + Src:V, + Targ:V ) is det.

For a dag edge Src-Targ (used in the depth first search) we update
label[Src] <-  max( label[Src], label[Targ] )
*/
dag_label( Src, Targ ) :-
    label( Src, Ls ),
    label( Targ, Lt ),
    ( Lt > Ls 
    ->  set_label( Src, Lt)
    ;   true
    ).

/*
backwards_label( + Src:V, + Targ:V ) is det.

Given a backwards edge Src-Targ, we update the label of Src as
label[Src] <- max( label[Src], dfsn[Targ] )
*/
backwards_label( Src, Targ ) :-
    label( Src , Ls ),
    dfs_num( Targ, Nt ),
    ( Nt > Ls
    ->  set_label( Src , Nt )
    ;   true
    ).
