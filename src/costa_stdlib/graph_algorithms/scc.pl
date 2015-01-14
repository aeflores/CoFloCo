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

:- module(scc, [compute_sccs/2]).

/* <module> Alforithm that computes the strongly connected components of 
a directed graph by employing a depth-first search. 

This algorithm was discovered by M. Sharir and its implementation is adapted 
from Baase and Van Gelder, Chapter 7.5. JPG 20/8/01

The module implementation is adapted from 
Type inference system (designed by M. Bruynooghe and J. Gallagher)
Version 1.0 created by jpg on 12/04/2005 (c) Roskilde University.


@license GPL
*/

:- use_module(stdlib(tree_234), [
    insert_tree/4, 
    search_tree/3, 
    traversekey_tree/2, 
    search_replace_tree/5
]).
:- use_module(stdlib(set_list),[
    insert_sl/3, 
    contains_sl/2,
    from_list_sl/2
]). 

/*
compute_sccs( 
    + DiGraph: list< V-V >, 
    - Strongly_Connected_Sets: set< ( recursivenes, set<V> ) >
) is det.

Computes the Strongly Connected Sets (SCS) of the directed graph DiGrpah. 
 * The Digraph is represented with the list of edges written as Source-Target.
    Loops, edges from one vertex to itself, are allowed, but repeated edges 
    between same source and target vertexes are ignored.
 * Strongly_Connected_Sets is a list of pairs (Rec, Set), where Set is the 
    strongly connected set of nodes and Rec is the recursiviness of the SCS. 

The recursivenes flag can have two values: 
 * 'non_recursive' means the strongly connected set is acyclic: it contains one
    single vertex Vert and the graph contains no loop Vert-Vert. 
 * 'recursive' means that the component is cyclic, which happens if it contains
    more than one vertex or it contains only one Vert with a loop.

Examples: 
 * compute_sccs( [], Sets)          ?       Sets = []. 
 * compute_sccs( [a-b], Sets)       ?
    Sets = [ (non_recursive, [b]), (non_recursive, [a]) ].
 * compute_sccs( [a-a], Sets)       ?       Sets = [ (recursive, [a])].
 * compute_sccs([a-b,a-a], Sets)    ?
    Sets = [ (non_recursive,[a]), (recursive,[b]) ].
 * compute_sccs([a-b,b-b], Sets)    ?
    Sets = [ (recursive,[b]), (non_recursive,[a]) ].
 * compute_sccs([a-b,b-a], Sets)    ?       Sets = [ (recursive,[a,b]) ].
 * compute_sccs( [a-b,b-c], Sets)   ?
    Sets = [ (non_recursive,[c]), (non_recursive,[b]), (non_recursive,[a]) ].
 * compute_sccs([a-b,b-c,b-c], Sets)    ?
    Sets = [ (recursive,[b,c]), (non_recursive,[a])].
 * compute_sccs([a-b,b-c,a-a,c-b], Sets) ?
    Sets = [ (recursive,[b,c]), (recursive,[a]) ]).
*/

compute_sccs( Edges, Strongly_Connected_Sets ) :-
    makeGraph( Edges, Graph ),
    scc_sharir(Graph, Sets0 ),
    prepare_sets( Sets0, Sets1 ), 
%   question: without this instruction, is the SCC lists topologically sorted?
%    from_list_sl( Sets1, Sets2 ),
    classify_sets( Sets1, Graph, Strongly_Connected_Sets ).

prepare_sets( [],[]). 
prepare_sets( [List|Lists], [Set|Sets] ) :- 
    from_list_sl( List, Set ), 
    prepare_sets( Lists, Sets ). 
    

% scc_sharir: the SCC procedure.
scc_sharir(root,[]) :- !.
scc_sharir(Graph,Sets) :-
    traversekey_tree(Graph,Nodes),
    dfs_stack(Nodes,Graph,root,_,[],Stack),
    dfs_sets(Stack,Graph,root,_,[],Sets),
    !.

/*
dfs_stack( Nodes, Graph, Marks, Marks_x, 
*/
dfs_stack( [], _Graph, Marks, Marks, Stack, Stack).
dfs_stack( [Node|Nodes], Graph, Marks, NMarks, Stack, NStack) :-
    dfs_stack_node( Node, Graph, Marks, Marks_x, Stack, Stack_x), 
    dfs_stack( Nodes, Graph, Marks_x, NMarks, Stack_x, NStack ).

/*
*/
dfs_stack_node( Node, _Graph, Marks, Marks, Stack, Stack) :- 
    search_tree( Marks, Node, black), 
    % N already visited
    !.
dfs_stack_node( Node, Graph, Marks, NMarks, Stack, [Node| NStack] ) :-
    insert_tree( Marks, Node, black, Marks_x),   % mark node as visited
    search_tree( Graph, Node, links( Succs,_) ), 
    dfs_stack( Succs, Graph, Marks_x, NMarks, Stack, NStack).

/*
dfs_sets( Nodes, Graph, Marks, NMarks, Sets, NSets )

phase 2:  use the depth-first ordering from phase 1
to traverse the transposed graph.
*/
dfs_sets([], _Graph, Marks, Marks, Sets, Sets ).
dfs_sets([Node|Nodes], Graph, Marks, NMarks, Sets, NSets) :-
    dfs_sets_x( Node, Graph, Marks, Marks_x, Sets, Sets_x), 
    dfs_sets(Nodes, Graph, Marks_x, NMarks, Sets_x, NSets).
     
dfs_sets_x( Node, _Graph, Marks, Marks, Sets, Sets) :- 
    search_tree( Marks, Node, black ),
    !.
dfs_sets_x( Node, Graph, Marks, Marks_x, Sets, [Set|Sets]) :- 
    dfs_sets_node(Node, Graph, Marks, Marks_x, [] ,Set). 

dfs_sets_node( Node, _Graph, Marks, Marks, Set, Set) :- 
    search_tree( Marks, Node, black ),
    !.
dfs_sets_node(Node, Graph, Marks, NMarks, Set, NSet) :-
    insert_tree( Marks, Node, black, Marks_x),  % mark node as visited
    search_tree( Graph, Node, links(_,Preds) ),
    dfs_each( Preds, Graph, Marks_x, NMarks, [Node|Set], NSet ).

dfs_each( [], _Graph, Marks, Marks, Set, Set ).
dfs_each( [Node|Nodes], Graph, Marks, NMarks, Set, NSet) :-
    dfs_sets_node( Node, Graph, Marks, Marks_x, Set, Set_x), 
    dfs_each( Nodes, Graph, Marks_x, NMarks, Set_x, NSet). 

/*
classify_sets( + Sets:list<set<V>> , + Graph:graph<V>, - Pairs )

*/
classify_sets( [] , _Graph, [] ).
classify_sets( [Set|Sets], Graph, [ (Recurs, Set) |Pairs] ) :- 
    recursivity_set( Set, Graph, Recurs ),
    classify_sets( Sets, Graph, Pairs ).

recursivity_set( [Vert], Graph, non_recursive ) :-
    \+ direct_recursive(Vert,Graph),
    !.
recursivity_set( _Set, _Graph, recursive ). 

direct_recursive(Vert,Graph) :-
    search_tree(Graph,Vert,links(Ss,_)),
    contains_sl(Ss,Vert).


/*
make_graph( + Edges:list<V-V> , - Graph: graph<V> ) is det.

type graph<V> = tree_234< V , links( set<V> , set<V> ) >.

It decodes the representation of the graph as a list of edges V-V and builds 
another representation as a table that maps each Vertexes to its predecessors
( vertexes Pred such that there is some link Pred-Vert in Edges)  and its 
successors ( vertexes Succ such that there is a link Vert-Succ in Edges). 

Starting from a list of links, make an adjacency list representation of the 
graph and the transposed graph (reversing links).


*/
makeGraph( Edges, Graph) :- makeGraph_x( Edges, root, Graph ). 

makeGraph_x( [], Graph, Graph ).
makeGraph_x( [Edge|Edges], Graph, NGraph ) :-
    makeGraph_xx( Edge, Graph, Graph_x ),
    makeGraph_x( Edges, Graph_x, NGraph ).

makeGraph_xx( Src-Targ , Graph, NGraph) :- 
    insert_succ( Src, Targ, Graph, Graph_x ),
    insert_pred( Targ, Src, Graph_x, NGraph ).

insert_succ( Src, Targ, Graph, NGraph ) :-
	search_replace_tree( Graph, Src, links(Ps,Ss), NGraph, links(NPs,Ss) ),
	!,
	insert_sl( Ps, Targ, NPs ).
insert_succ( Src, Targ, Graph, NGraph ) :-
	insert_tree( Graph, Src, links([Targ],[]), NGraph ).

insert_pred( Targ, Src, Graph, NGraph ) :-
	search_replace_tree( Graph, Targ, links(Ps,Ss), NGraph, links(Ps,NSs) ),
	!,
	insert_sl( Ss, Src, NSs ).
insert_pred( Targ, Src, Graph, NGraph ) :-
	insert_tree( Graph, Targ, links([],[Src]), NGraph ).
