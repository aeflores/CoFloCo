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

:- module(tree_234, [
    empty_tree/1,
    insert_tree/4, 
    search_tree/3, 
    traversekey_tree/2, 
    search_replace_tree/5, 
    traverse_tree/2,
    make_tree/2
]).

/** <module> A single-valued map of Keys to Values, implemented with a 234 tree.

Tree with records and no children

There are three constructors: 

type tree_234<K,V>  ::= root    
    |   leaf( Recs)          where   Recs:map<K,V>
    |   node( Recs, Subs)   where   Recs:map<K,V>, Subs:list<tree_234<K,V> > 

 * Recs is non empty, sorted by keys
 *length(Childs) = length(Recs)+1
   *At least one Child is not empty
   * let be Key(i) the key of the record in (Recs !! i)  
     Childs[i] only contains Records rec(K,_) such that Key(i-1) @=< K @=< Key(i)
*/

:- use_module(stdlib(list_utils),[set_lu/4,insert_lu/4,append_lu/3]).
:- use_module(stdlib(list_map),[insert_lm/4,lookup_lm/3, keys_lm/2, update_lm/5]).

/*
empty_tree( - Tree:tree<K,V> ) is det. 

T is the tree with no key or value. 
*/
empty_tree(root).

/*
insert_tree( + Tree:tree<K,V>, + Key:K, + Val:V, - NTree:tree<K,V>) is det.

NTree is the result of inserting the pair (Key,Val) in Tree. 
If Tree contains a record for Key, then the value Val is overwritten. 
*/
insert_tree(Tree,Key,Val,NTree) :-
    insert_base_tree(Tree,Key,Val,Tree1),
    ( split_big_tree( Tree1, Left, Rec, Right)
    ->  NTree = node( [Rec], [Left, Right] )
    ;   NTree = Tree1
    ). 

insert_base_tree(root ,Key,Val,leaf( [ (Key,Val)] ) ).
insert_base_tree(leaf(Recs),Key,Val,leaf(NRecs)) :-
    insert_lm(Recs,Key,Val,NRecs).
insert_base_tree(node(Recs,Succs),Key, Val, node(NRecs,NSuccs)) :-
    insert_node( Recs, Succs, Key, Val, NRecs, NSuccs). 

insert_node( [], [Succ], Key, Val, NRecs, NSuccs ) :- 
    insert_base_tree(Succ,Key,Val, Succ_1 ),
    ( split_big_tree( Succ_1, Left, Rec_x, Right )
    ->  NRecs  = [Rec_x], 
        NSuccs = [Left,Right]
    ;   NRecs  = [],
        NSuccs = [ Succ_1]
    ).
insert_node( [Rec|Recs], [Succ|Succs] , Key, Val, [NRec|NRecs], [NSucc|NSuccs]) :- 
    Rec = ( RKey, _RVal), 
    compare( Comp, RKey, Key), 
    insert_node_x( Comp, [Rec|Recs], [Succ|Succs] , Key, Val, [NRec|NRecs], [NSucc|NSuccs]). 

insert_node_x( <, [Rec|Recs], [Succ|Succs] , Key, Val, [Rec|NRecs], [Succ|NSuccs]) :- 
    insert_node( Recs, Succs, Key, Val, NRecs, NSuccs).
insert_node_x( =, [_Rec|Recs], Succs , Key, Val, [NRec|Recs], Succs) :- 
    NRec = ( Key, Val).
insert_node_x( >, Recs, [Succ|Succs] , Key, Val, NRecs, NSuccs) :- 
    insert_base_tree( Succ, Key, Val, Succ_1 ),
    ( split_big_tree( Succ_1, Left, Rec_x, Right )
    ->  NRecs  = [Rec_x|Recs], 
        NSuccs = [Left,Right|Succs]
    ;   NRecs  = Recs,
        NSuccs = [ Succ_1 | Succs]
    ).

% split_big_tree: if it has 4 or more records, splits it 
split_big_tree( leaf( [R1,R2,R3,R4] ), Left, R2, Right ) :- 
    Left  = leaf( [R1] ), 
    Right = leaf( [R3,R4]).
split_big_tree( node( [R1,R2,R3,R4], [S1,S2|Ss] ), Left, R2, Right) :- 
    Left  =  node( [R1], [S1,S2] ), 
    Right =  node( [R3,R4], Ss ).

/*
search_tree( + Tree: tree<K,V>, + Key:K, - Val:V ) is semidet.  

If Tree contains a record for Key then it unifies Val with the recorded value 
and the predicate succeeds. If Tree contains no record for Key, it fails. 
*/
search_tree(leaf(Recs),Key,Val) :- lookup_lm(Recs, Key, Val).
search_tree(node(Recs,Subs),Key,Val) :-
    search_node( Recs, Subs, Key, Val). 

search_node( [], [Sub], Key, Val) :-
    search_tree( Sub, Key, Val).
search_node( [Rec|Recs], Subs, Key, Val) :-
    Rec = (RKey,_RVal),
    compare(Comp, RKey, Key),
    search_node_x( Comp, [Rec|Recs], Subs, Key, Val ).
    
search_node_x( < , [_Rec|Recs], [_Sub|Subs], Key, Val ) :- 
    search_node( Recs, Subs, Key, Val).
search_node_x( = , [Rec|_Recs], _Subs, _Key, Val ) :- 
    Rec = ( _, Val).
search_node_x( > , _Recs, [Sub|_Subs], Key, Val ) :- 
    search_tree( Sub, Key, Val).
   
/*
search_replace_tree(
    + Tree:tree<K,V>, + Key:K, + NVal:V   - OVal:V, - NTree:tree<K,V>,
)  is det. 

Searches the record of Key in Tree, retrieves the previous value OVal and 
gives NTree as replacing OVal with NVal in that record. 
 * Tree : the old tree (before replacing the value)
 * Key : the key which value is replaced
 * OVal: the value of K in the tree T. 
 * NTree: the new Tree (after replacing).
 * NVal: the new value 
*/
search_replace_tree( leaf(Recs),Key,OVal,leaf(NRecs),NVal) :-
    update_lm( Recs, Key, OVal, NVal, NRecs). 
search_replace_tree( node(Recs, Subs), Key,OVal, node(NRecs,NSubs) ,NVal) :-
    replace_node(Recs,Subs,Key,OVal,NVal,NRecs,NSubs).

replace_node( [], [Sub],Key,OVal,NVal, [],[NSub]) :-
    search_replace_tree( Sub, Key, OVal, NSub, NVal). 
replace_node([Rec|Recs],[Sub|Subs],Key,OVal,NVal,[NRec|NRecs],[NSub|NSubs]) :-
    Rec = ( RKey, _RVal),
    compare( Comp, RKey, Key), 
    replace_node_x( Comp, [Rec|Recs],[Sub|Subs],Key,OVal,NVal,[NRec|NRecs],[NSub|NSubs]).
    
replace_node_x( <, [Rec|Recs],[Sub|Subs],Key,OVal,NVal,[Rec|NRecs],[Sub|NSubs]) :- 
    replace_node( Recs, Subs, Key, OVal, NVal, NRecs, NSubs ).
replace_node_x( =, [Rec|Recs],[Sub|Subs],_Key,OVal,NVal,[NRec|Recs],[Sub|Subs]) :- 
    Rec = ( RKey, RVal),
    NRec = (RKey, NVal),
    OVal = RVal.
replace_node_x( >, [Rec|Recs],[Sub|Subs],Key,OVal,NVal,[Rec|Recs],[NSub|Subs]) :- 
    search_replace_tree( Sub, Key, OVal, NSub, NVal). 

/*
traversekey_tree( + Tree:tree<K,V>, - Keys:list<K>) is det. 

Gives the set of keys of the Tree.  
*/
traversekey_tree( Tree, Keys) :- 
    traverse_tree( Tree, Map), 
    keys_lm( Map, Keys). 

/*
traverse_tree( + Tree: tree<K,V>, - Map:map<K,V> ) is det. 

traverse the tree in order, returning the records in a list
*/
traverse_tree(Tree,Map) :- trav_tree(Tree,[],Map).

% trav_tree : auxiliar predicate, immersion
trav_tree(root,Map,Map).
trav_tree(leaf(Recs),Map1,Map) :- append_lu( Recs, Map1, Map). 

trav_tree( node( Recs, Subs), Map1, Map) :- 
    trav_treenode( Recs, Subs, Map1, Map). 

trav_treenode( [],[Sub],Map1,Map) :-
    trav_tree(Sub,Map1,Map).
    
trav_treenode( [Rec|Recs],[Sub|Subs],Map2,Map) :-
    trav_tree(Sub,[Rec|Map1],Map),
    trav_treenode( Recs,Subs,Map2,Map1).

/*
make_tree ( + Recs:list<(K,V), - Tree:tree<K,V> ) is det. 

Tree is a Tree that contains all the records in Recs 
*/
make_tree( Recs, Tree) :- make_tree_x( Recs, root, Tree).

make_tree_x( [], Tree, Tree).
make_tree_x( [Rec|Recs], Tree_x, Tree) :-
    make_tree_xx( Rec, Tree_x, Tree_xx),
    make_tree_x( Recs, Tree_xx, Tree).

make_tree_xx( Rec , Tree_x, Tree_xx ) :-
    Rec = ( Key, Val),
    insert_tree( Tree_x, Key, Val, Tree_xx).
