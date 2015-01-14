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

:- module(utils,[
		 ut_eval_cost_function/4,
		 ut_arithmetic_eval/2,
		 ut_lower_upper/2,
		 ut_length/2,
		 ut_member/2,
		 ut_var_member/2,
		 ut_var_member_chk/2,
		 ut_chk_member/2,
		 ut_variant_member/3,
		 ut_append/3,
		 ut_split_at_pos/4,
		 ut_flat_list/2,
		 ut_append_lists/2,
		 ut_between/3,
		 ut_atoms_concat/2, 
		 ut_atom_concat/3,
		 ut_max/3,
		 ut_max_list/2,
		 ut_min/3,
		 ut_min_list/2,
		 ut_indexes_to_bitmap/2, 
		 ut_bitmap_to_indexes/2, 
		 ut_number_to_atom/2,
		 ut_varset/2, 
		 ut_select/4, 
		 ut_ith/5,
		 ut_atom_codes/2,
		 ut_not_member/2,
		 ut_sort/2,
		 ut_sort_rdup/2,
		 ut_pairlist_sort/2,
		 ut_number_vars/2,
		 ut_remove/3,
		 ut_difference/3,
		 ut_remove_duplicates/2,
		 ut_remove_repetitions/3,
		 ut_remove_repetitions_and_numbers/3,
		 ut_variant/2,
		 ut_delete/3,
		 ut_nonvar_delete/3,
		 ut_reverse/2,
		 ut_last/2,
		 ut_file_exists/1,
		 ut_list_to_dlist/2,
		 ut_search_replace_char/4,
		 ut_remove_n_elemens/3,
		 ut_sub_list/3,
		 ut_sub_list_interval/4,
		 ut_nth/3,
		 ut_replace_nth/4,
		 ut_sum_list/2,
		 ut_log/3,
		 ut_copy_file/2,
		 ut_copy_stream/2,
		 ut_read_stream/2,
		 ut_read_stream_line/2,
		 ut_read_stream_line_list/2,
		 ut_write_stream/2,
		 ut_write_stream_line/2,
		 ut_write_stream_line_list/2,
		 ut_list_union/3,
		 ut_list_intersection/3,
		 ut_split_path/2,
		 ut_trim/2,
		 ut_split_atom/3,
		 ut_cputime/1,
		 ut_cputime_to_runtime/3,
		 ut_cputimes_to_runtimes/2,
		 ut_file_name_ext/3,
		 ut_basename/2,
		 ut_extension/2,
		 ut_no_path_filename/2, 
		 ut_print_list/1,
		 ut_varset_withoutorder/2, 
		 ut_subseteq/2
		]).


%% ut_eval_cost_function(+Call,+Head,+Body,-Value)
%
%  allows evaluating a cost function for a concrete Call into a
%  Value. For this, the cost function is represented using two terms:
%  Head and Body.

ut_eval_cost_function(Call,Head,Body,Value):-
	copy_term((Head,Body),(HeadC,BodyC)),
	Call = HeadC,
	ut_arithmetic_eval(BodyC,Value).

% ut_arithmetic_eval(+Exp,-Val)
%
%  Exp is an arithmetic expression, of value Val. Besides +, -, * and
%  /, it accepts pow (powers and exponentials) and log/1 and log/2
%  (logarithms in base 2 and in base N) and max/2 and max/1 (max of a
%  list).
%
%  Example:
%
%  Z=3*A+pow(B,2), A=1, B=4, ut_arithmetic_eval(Z,V)
%
%  V will be 3*1+4**2=19.
%

ut_arithmetic_eval(E,X) :-
	number(E), !,
	X is E.

ut_arithmetic_eval(E,X) :-
	compound(E),
	E =.. [F, A1, A2], 
	ut_arithmetic_eval(A1,X1),
	ut_arithmetic_eval(A2,X2),
	(
	 + == F,
	 X is X1+X2
	;
	 - == F,
	 X is X1-X2
	;
	 * == F,
	 X is X1*X2
	;
	 / == F,
	 X is X1/X2
	;
	 pow == F,
	 X is X1**X2
	;
	 log == F,
	 ut_log(X1,X2,X)
	;
	 max == F,
	 ut_max(X1,X2,X)
	), !.

ut_arithmetic_eval(E,X) :-
	compound(E),
	E =.. [F , Arg], 
	(
	 log == F,
	 ut_arithmetic_eval(Arg,XN),
	 ut_log(2,XN,X)
	;
	 F == max,
	 Arg = [_|_], % list(L)
	 findall(V,(member(E_p,Arg),ut_arithmetic_eval(E_p,V)),Vs),
	 ut_max_list(Vs,X)
	;
	 nat == F,
	 ut_arithmetic_eval(Arg,TmpX),
	 ut_max(TmpX,0,X)
	;
	 - == F,
	 ut_arithmetic_eval(Arg,TmpX),
	 X is -TmpX
	;
	 sqrt == F,
	 ut_arithmetic_eval(Arg,TmpX),
	 X is sqrt(TmpX)
	), !.



% ut_lower_apper(LowerString,UpperString)
%
%   Converts from upper to lower, or from lower to upper
%

ut_lower_upper([],[]) :- !.

% [a..z] -> [A..Z]
ut_lower_upper([L|LowerString],[U|UpperString]) :-
	number(L),
	L >= 97, L =< 122,
	U is L-32, !,
	ut_lower_upper(LowerString,UpperString).

% [A..Z] -> [a..z]
ut_lower_upper([L|LowerString],[U|UpperString]) :-
	number(U),
	U >= 65, U =< 90,
	L is U+32, !,
	ut_lower_upper(LowerString,UpperString).

% Any other character not in [A..Z] or [a..z]
ut_lower_upper([L|LowerString],[L|UpperString]) :-
	ut_lower_upper(LowerString,UpperString).






ut_length(L,N) :-
        nonvar(L),
        !,
        ut_length_1(L,0,N).
ut_length(L,N) :-
        integer(N),
        N >= 0,
        !,
        ut_length_2(N,L).


ut_length_1(L,N,N) :-
        nonvar(L),
        L = [],
        !.
ut_length_1(L,Accm,N) :-
        nonvar(L),
        L = [_|As],
        NewAccm is Accm+1,
        ut_length_1(As,NewAccm,N).

ut_length_2(0,[]) :- !.
ut_length_2(N,[_|As]) :-
        N>0,
        !,
        NewN is N-1,
        ut_length_2(NewN,As).



%
%
ut_member(X,[X|_]).
ut_member(X,[_|Xs]) :- ut_member(X,Xs).

ut_not_member(_,[]):-!.
ut_not_member(X,[X1|Xs]) :- X1 \== X,ut_not_member(X,Xs).


ut_var_member(X,[Y|_])  :- X == Y.
ut_var_member(X,[_|Xs]) :- ut_var_member(X,Xs).

ut_var_member_chk(X,[Y|_])  :- 
	X == Y,
	!.
ut_var_member_chk(X,[_|Xs]) :- 
	ut_var_member_chk(X,Xs).

ut_chk_member(X,[Y|_])  :- ut_variant(X,Y),!.
ut_chk_member(X,[_|Xs]) :- ut_chk_member(X,Xs).

ut_variant_member(X,[Y|_],Y)  :- ut_variant(X,Y),!.
ut_variant_member(X,[_|Xs],Y) :- ut_variant_member(X,Xs,Y).



% ut_append( As , Bs , Cs ) :: ( [a] , [a] , [a] )
%
% Cs is the list that result of appending Bs after As. 
%
% example: ut_append([1,2],[3,4],[1,2,3,4]).
%
ut_append([],X,X).
ut_append([X|Xs],Ys,[X|Zs]) :- ut_append(Xs,Ys,Zs).


% ut_append_lists ( AAs , Bs )  :: ( [[a]], [a] )
%
% Bs is the result of concatenating all lists in AAs
%
% Example: ut_append_lists( [ [1,2],[3,4] ] , [1,2,3,4] )
% 
ut_append_lists([],[]).
ut_append_lists([A|As],Bs) :-
        ut_append_lists_aux(A,As,Bs).

ut_append_lists_aux([],As,Bs) :-
        ut_append_lists(As,Bs).
ut_append_lists_aux([X|Xs],As,[X|Bs]) :-
        ut_append_lists_aux(Xs,As,Bs).




ut_flat_list([],[]).
ut_flat_list([A|Bs],Cs) :-
	ut_flat_list_aux(A,Bs,Cs).

ut_flat_list_aux(A,Bs,[A|Cs]) :-
	var(A),
	!,
	ut_flat_list(Bs,Cs).
ut_flat_list_aux([],Bs,Cs) :-
	!,
	ut_flat_list(Bs,Cs).
ut_flat_list_aux([A|As],Bs,Cs) :-
	!,
	ut_flat_list_aux(A,[As|Bs],Cs).
ut_flat_list_aux(A,Bs,[A|Cs]) :-
	ut_flat_list(Bs,Cs).



%
%
ut_between(N,M,X) :- integer(N), integer(M), N =< M, between_aux(N,M,X).

between_aux(N,_M,N).
between_aux(N,M,X) :- N < M, NextN is N+1, between_aux(NextN,M,X).


%
%
ut_atoms_concat([],'').
ut_atoms_concat([A|As],Atom) :-
        ut_atoms_concat(As,Atom_aux),
        ut_atom_num_concat(A,Atom_aux,Atom).


ut_atom_num_concat(A,B,C) :-
	( atom(A) -> atom_codes(A,As); number_codes(A,As) ),
	( atom(B) -> atom_codes(B,Bs); number_codes(B,Bs) ),
	ut_append(As,Bs,Cs),
	atom_codes(C,Cs).
	  

ut_atom_concat(A,B,C) :-
	ut_atom_concat_aux(A,As),
	ut_atom_concat_aux(B,Bs),
	ut_atom_concat_aux(C,Cs),
	ut_append(As,Bs,Cs),
	atom_codes(A,As),
	atom_codes(B,Bs),
	atom_codes(C,Cs).

ut_atom_concat_aux(A,As)   :- atom(A), !, atom_codes(A,As).
ut_atom_concat_aux(_A,_As).




%%
%%
ut_max(A,B,A) :- A =:= B, !. 
ut_max(A,B,A) :- A > B, !.
ut_max(A,B,B) :- A < B, !.

%
%
ut_min(A,A,A) :-!.
ut_min(A,B,A) :- A < B, !.
ut_min(A,B,B) :- A > B, !.


%%
%%
ut_max_list([],0).
ut_max_list([X|Xs],Min) :-
	ut_max_list_aux(Xs,X,Min).

ut_max_list_aux([],Min,Min).
ut_max_list_aux([X|Xs],CurrMin,Min) :-
	X>CurrMin,
	!,
	ut_max_list_aux(Xs,X,Min).
ut_max_list_aux([_|Xs],CurrMin,Min) :-
	ut_max_list_aux(Xs,CurrMin,Min).


%
%
ut_min_list([X|Xs],Min) :-
	ut_min_list_aux(Xs,X,Min).

ut_min_list_aux([],Min,Min).
ut_min_list_aux([X|Xs],CurrMin,Min) :-
	X<CurrMin,
	!,
	ut_min_list_aux(Xs,X,Min).
ut_min_list_aux([_|Xs],CurrMin,Min) :-
	ut_min_list_aux(Xs,CurrMin,Min).


%
ut_bitmap_to_indexes(Is_Bitmap,Is) :-
        integer(Is_Bitmap),
        !,
        ut_bitmap_to_indexes_aux(Is_Bitmap,0,Is).

ut_indexes_to_bitmap(Is,Is_Bitmap) :-
        ground(Is),
        !,
        ut_indexes_to_bitmap_aux(Is,0,Is_Bitmap).

ut_indexes_to_bitmap_aux([],Accm_Bitmap,Accm_Bitmap).
ut_indexes_to_bitmap_aux([I|Is],Accm_Bitmap,Bitmap) :-
        New_Accm_Bitmap is Accm_Bitmap \/ (1<<I),
        ut_indexes_to_bitmap_aux(Is,New_Accm_Bitmap,Bitmap).

ut_bitmap_to_indexes_aux(0,_I,[]).
ut_bitmap_to_indexes_aux(BitMap,N,Is) :-
        BitMap > 0,
	Bit is BitMap /\ 1,
	( Bit ==  1 -> Is=[N|Is_aux] ; Is=Is_aux),
        New_BitMap is BitMap>>1,
        New_N is N+1,
        ut_bitmap_to_indexes_aux(New_BitMap,New_N,Is_aux).



%
%
ut_number_to_atom(N,A) :-
        number(N),
        !,
        number_codes(N,As),
        atom_codes(A,As).
ut_number_to_atom(N,A) :-
        atom(A),
        !,
        atom_codes(A,As),
        number_codes(N,As).




% ut_varset( Term , Vars)  :: ( Any , [Var] )
%
% Vars is the set of Variables in Term, sorted syntactically.  
%
ut_varset(X,Xs) :-
        ut_varsbag(X,Xs_uns),
        ut_sort_rdup(Xs_uns,Xs),
	!.

ut_varset_withoutorder(X,Xs) :-
        ut_varsbag(X,Xs),
        %ut_sort_rdup(Xs_uns,Xs),
	!.

% ut_varbag( Term , Vars)  :: ( Any , [Var] )
%
% Vars is the list of free Variables in Term,
% fetched by traversing Term in preorder. 
%
% 
ut_varsbag(Term,Vs) :-
        ut_varsbag_aux(Term,Vs,[]).

ut_varsbag_aux(X,Vars,Tail) :-
        var(X),!,
        Vars = [X|Tail].
ut_varsbag_aux([H|T],Vars,Tail) :-
        !,
        ut_varsbag_aux(H,Vars,Tail0),
        ut_varsbag_aux(T,Tail0,Tail).
ut_varsbag_aux(Term,Vars,Tail) :-
        functor(Term,_,A),
        go_inside(1,A,Term,Vars,Tail).

go_inside(N,MaxN,_,Tail,Tail) :-
        N>MaxN, !.
go_inside(N,MaxN,T,Bag,Tail) :-
        Nth is N+1,
        arg(N,T,ARG),
        ut_varsbag_aux(ARG,Bag,Tail0),
        go_inside(Nth,MaxN,T,Tail0,Tail).


%
% This predicate removes duplicates from a sorted list.
% 
ut_remove_duplicates(A,B) :-
        remove_duplicates(A,_Dummy_Element,B).

remove_duplicates([],_Last_Element,[]).
remove_duplicates([A|As],Last_Element,Bs) :-
        A == Last_Element,
        !,
        remove_duplicates(As,Last_Element,Bs).
remove_duplicates([A|As],_Last_Element,[A|Bs]) :-
        remove_duplicates(As,A,Bs).




% ut_sort ( Uns , Sor ) :: ( [a] , [a] )
% 
% Sor is the same as Uns but with the elements sorted SYNTACTICALLY. 
ut_sort(Xs_uns,Xs) :-
        qs(Xs_uns,Xs,[]),
	!.

qs([], T, T).
qs([X | Xs], S, T) :- pt(Xs, X, L, G), qs(L, S, [X | M]), qs(G, M, T).

pt([], _, [], []).
pt([X | Xs], M, L, [X | G]) :- X @> M, !, pt(Xs, M, L, G).
pt([X | Xs], M, [X | L], G) :- pt(Xs, M, L, G).



ut_sort_rdup(Xs_uns,Xs) :-
        ut_sort(Xs_uns,Xs_aux),
        ut_remove_duplicates(Xs_aux,Xs),
	!.


% sorts a list of pairs of terms, sorting BEFORE the pairs, THEN the
% list
% 
ut_pairlist_sort(Xs_uns,Xs) :-
	ut_pairs_sort(Xs_uns,Xs_p),
	ut_sort_rdup(Xs_p,Xs).


ut_pairs_sort([],[]).
ut_pairs_sort([(X1,Y1)|PS1],[(Y1,X1)|PS2]) :-
	Y1 @< X1,
	ut_pairs_sort(PS1,PS2).
ut_pairs_sort([(X1,Y1)|PS1],[(X1,Y1)|PS2]) :-
	ut_pairs_sort(PS1,PS2).


% ut_delete ( As , A , Bs) :: ([a], a , [a])
%
% Bs is the result of deleting from As ALL the appearances of A, 
% when an appearance is determined with sintactic equality. 
%
ut_delete([],_Y,[]).
ut_delete([X|Xs],Y,Ys) :- 
	X == Y,
	!,
	ut_delete(Xs,Y,Ys).
ut_delete([X|Xs],Y,[X|Ys]) :- 
	ut_delete(Xs,Y,Ys). 



% ut_nonvar_delete ( As , A , Bs) :: ([a], a , [a])
%
% Bs is the result of deleting from AS 
% THE FIRST element that UNIFIES with A ,
%
% Examples:  ut_nonvar_delete( [f(1),g(2),h(3)] , g(X) , [f(1),h(3)]) {X=2}

ut_nonvar_delete([],_Y,[]).
ut_nonvar_delete([X|Xs],X, Xs) :- !.
ut_nonvar_delete([X|Xs],Y,[X|Ys]) :- 
	ut_nonvar_delete(Xs,Y,Ys). 


% ut_select (Xs , X , Pres, Posts) :: ( [a] , a , [a] , [a] )
% 
%  Splits the lists in two parts,
% Pres are the elements before X and Posts are the elements after X. 
% Equation :: Xs = Pres ++ [X] ++ Posts 
%
% The predicate fails if X is not a member (Unification = ) of  Xs
%
% Example : ut_select ( [a,b,c,d,e] , b , [a] , [c,d,e]) 
ut_select([X|Xs],X,[],Xs).
ut_select([X|Xs],A,[X|Ys],Zs) :-
        ut_select(Xs,A,Ys,Zs).


% ut_ith(N, Xs , X , Pres, Pos) :: ( number , [a] , a , [a] , [a] )
%
% Splits the list by its N-th element, in three parts: 
% - X is the n-th element of Xs (being the first one the 0-th element), 
% - Pres is the list of N first elements of Xs. 
% - Posts are the rest of elements of Xs after the n-th element (X). 
%  
% The predicate fails if N > length(Xs). 
%
% Example :: ut_ith ( 2 , [a,b,c,d,e,f] , c , [a,b] , [d,e,f] )  
ut_ith(0,[X|Xs],X,[],Xs) :- !.
ut_ith(N,[X|Xs],IthV,[X|Pres],Posts) :-
        N>0,
        N1 is N-1,
        ut_ith(N1,Xs,IthV,Pres,Posts).

%
%
ut_atom_codes(A,B):- ground(A), !, ut_atom_codes_aux(A,B).
ut_atom_codes(A,B):- atom_codes(A,B).

ut_atom_codes_aux(A,B):- atom(A),   !, atom_codes(A,B).
ut_atom_codes_aux(A,B):- number(A), !, number_codes(A,B).


%%
%%
ut_number_vars(Atom, List_of_atoms) :-
	ut_varset(Atom, Vs),
	ut_number_vars_aux(Vs, '', 0, List_of_atoms, List_of_atoms).

ut_number_vars_aux([], _Suff, _N, _As, _List_of_atoms):-!.
ut_number_vars_aux([V|Vs], Suff, N, [A|As], List_of_atoms) :-
	ut_atoms_concat([A,Suff],V),!,
	ut_number_vars_aux(Vs, Suff, N, As, List_of_atoms).
ut_number_vars_aux(Vs, _Suff, N, [], List_of_atoms) :-
	Next_N is N+1,
	ut_number_to_atom(Next_N, Next_Suff),!,
	ut_number_vars_aux(Vs, Next_Suff, Next_N, List_of_atoms, List_of_atoms).



%%
%%
ut_remove_repetitions([],_,[]):-!.
ut_remove_repetitions([X|Xs],L,NL):-
   ut_var_member(X,L),
   !,
   ut_remove_repetitions(Xs,L,NL).
ut_remove_repetitions([X|Xs],L,[X|NL]):-
   ut_remove_repetitions(Xs,[X|L],NL),!.


%%%%%%%%
ut_remove_repetitions_and_numbers([],_,[]):-!.
ut_remove_repetitions_and_numbers([X|Xs],L,NL):-
   nonvar(X),!,  
   ut_remove_repetitions_and_numbers(Xs,L,NL).

ut_remove_repetitions_and_numbers([X|Xs],L,NL):-
   ut_var_member(X,L),
   !,
   ut_remove_repetitions_and_numbers(Xs,L,NL).
ut_remove_repetitions_and_numbers([X|Xs],L,[X|NL]):-
   ut_remove_repetitions_and_numbers(Xs,[X|L],NL),!.



%%
%%
ut_variant(A,B) :-
	\+ \+ ut_variant_aux(A,B).

ut_variant_aux(A,B) :-
	numbervars(A,0,_),
	numbervars(B,0,_),
	A = B.


%%
%%
ut_reverse(Xs,Ys):- 
	reverse_ac(Xs,[],Ys).

reverse_ac([], L, L).
reverse_ac([X|Xs],L,R) :- 
	reverse_ac(Xs,[X|L],R).

%%
%%
ut_last([X|Xs],Last):- 
	(Xs = [] ->
	    Last = X
	;
	    ut_last(Xs,Last)
	).





%%
%%
ut_list_to_dlist([],T-T).
ut_list_to_dlist([X|Xs],[X|H]-T) :-
	ut_list_to_dlist(Xs,H-T).



%
%
ut_search_replace_char(Atom_A, S, R, Atom_B) :-
	atom_codes(Atom_A, Atom_A_Codes),
	atom_codes(S,[SC]),
	atom_codes(R,[RC]),
	ut_search_replace_char_aux(Atom_A_Codes, SC, RC, Atom_B_Codes),
	atom_codes(Atom_B,Atom_B_Codes).


ut_search_replace_char_aux([], _S, _R, []).
ut_search_replace_char_aux([S|As], S, R, [R|Bs]) :-
	!,
	ut_search_replace_char_aux(As, S, R, Bs).
ut_search_replace_char_aux([X|As], S, R, [X|Bs]) :-
	ut_search_replace_char_aux(As, S, R, Bs).



% ut_remove_n_elements(N, Xs , Ys ) :: ( integer , [a] , [a] )
% YS is the result of eliminating the first n elements from Xs. 
% 
% 
% Precondition: length(Xs) >= N, otherwise it fails. 
%
% 
ut_remove_n_elemens(0,Xs,Xs).
ut_remove_n_elemens(N,[_|Xs],Ys) :-
	N>0,
	!,
	N1 is N-1,
	ut_remove_n_elemens(N1,Xs,Ys).
% additional rule for avoid fails 
% ut_remove_n_elements(_,[],[]). 


% ut_sub_list ( List , Indices , Sublist ) :: ( [a] , [integer] , [a])
% Sublist is the List which contains those elements from List 
% at the positions described by Indices. 
%
% WARNING: Indices must be a sorted list. Otherwise, it ommits unsorted indices 
% Example: ut_sub_list ( L , [1,3], LS) is the same to  ut_sub_list ( L , [1,3,2], LS)
%
%
ut_sub_list(List,Indices,SubList) :-
	ut_sub_list_aux(List,Indices,0,SubList).

ut_sub_list_aux([],[],_,[]).
ut_sub_list_aux([X|Xs],[I|Is],I,[X|Ys]) :-
	!,
	I1 is I+1,
	ut_sub_list_aux(Xs,Is,I1,Ys).
ut_sub_list_aux([_|Xs],Is,I,Ys) :-
	!,
	I1 is I+1,
	ut_sub_list_aux(Xs,Is,I1,Ys).


%% ut_sub_list_interval (start bound included, end bound excluded)
%%
ut_sub_list_interval(List,Start,End,[El|SubList]) :-
	Start < End,
	ut_nth(Start,List,El),
	Start1 is Start+1,
	ut_sub_list_interval(List,Start1,End,SubList).
ut_sub_list_interval(_List,Start,End,[]) :-
	Start >= End.

%% ut_split_at_pos(+List,+Pos,-L1,-L2)
%%Example: ut_split_at_pos([a,b,c],2,[a,b],[c])
%%Example: ut_split_at_pos([a,b,c],0,[],[a,b,c])
%%Example: ut_split_at_pos([a,b,c],5,[a,b,c],[])
ut_split_at_pos(List,Pos,L1,L2) :-
	ut_length(List,Length),
	(Pos > Length -> Pos_p = Length ; Pos_p = Pos),
	ut_append(L1,L2,List),
	ut_length(L1,Pos_p).


ut_nth(A,B,C) :-
	number(A),
	!,
	ut_nth_1(A,B,C).

ut_nth(A,B,C) :-
	ut_nth_2(B,1,A,C).


ut_nth_1(1,[X|_],X).
ut_nth_1(N,[_|Xs],X) :-
	N>1,
	N1 is N-1,
	ut_nth_1(N1,Xs,X).

ut_nth_2([X|_],N,N,X).
ut_nth_2([_|Xs],N1,N,X) :-
	N2 is N1+1,
	ut_nth_2(Xs,N2,N,X).


%% replace_nth(L,I,V,L') => L' is the list resulting from replacing
%  the I-th element of L by V.
ut_replace_nth([_|Old],1,Value,[Value|Old]).
ut_replace_nth([X|Old],Index,Value,[X|New]) :-
	Index > 1,
	Index1 is Index - 1,
	ut_replace_nth(Old,Index1,Value,New).


% ut_sum ( L , S) :: ( [number] , number)
% S is the sum of all elements in L
ut_sum_list(L,N):-ut_sum_list_aux(L,0,N).

ut_sum_list_aux([],N,N):-!.
ut_sum_list_aux([X|Xs],Acu,N):-
   Acu1 is Acu+X,
   ut_sum_list_aux(Xs,Acu1,N).


%
% ut_remove(LA , A , LD) ::  ( [a] , A , [a] )
%
% LD is the result of removing from LA the first element 
% which is LITERALLY equal to A. 
%
ut_remove([],_,[]).
ut_remove([E1|L1],E2,L1) :-
	E1==E2, !.
ut_remove([El1|L1],El,[El1|L]) :-
	ut_remove(L1,El,L).	


% ut_difference (LA , LB , LD ) :: ( [a] , [a] , [a] )
%
% LD is the result of removing form LA the first appearance of every element in LB. 
ut_difference(L1,[],L1).
ut_difference(L1,[E|ES],L) :-
	ut_remove(L1,E,L2),
	ut_difference(L2,ES,L).


%
% ut_log (Base,Exp,Res)  :: ( number , number , number)
%
% Evaluates the logarithm with some Base of a Number
% Intended use mode : (ground , ground , var). 
%
ut_log(Base,Exp,Res) :-
    Res is log(Exp) / log(Base).



%
%
ut_file_exists(File) :-
	catch(open(File,read,Stream),_,fail),
	close(Stream).


%
%
ut_copy_file(Path1,Path2) :-
	open(Path1,read,Stream1),
	open(Path2,write,Stream2),
	ut_copy_stream(Stream1,Stream2),
	close(Stream1),
	close(Stream2).

%
%
ut_copy_stream(Stream1,Stream2) :-
	get_code(Stream1,CD),
	(
	 CD == -1 ->
	 true
	;
	 atom_codes(CH,[CD]),
	 write(Stream2,CH),	 
	 ut_copy_stream(Stream1,Stream2)
	).


% gets a list of CODES
%
ut_read_stream(Stream,CDS) :-
	get_code(Stream,CD),
	(
	 CD == -1 ->
	 CDS = []
	;
	 ut_read_stream(Stream,CDS0),
	 CDS = [CD|CDS0]
	).


% gets a list of CODES
%
ut_read_stream_line(Stream,Line) :-
	get_code(Stream,CD),
	(
	 CD == -1 ->
	 Line = []
	;
	 (
	  CD == 10 ->
	  Line = []
	 ;
	  ut_read_stream_line(Stream,Line0),
	  Line = [CD|Line0]
	 )
	).


% gets a list of lists of CODES
%
ut_read_stream_line_list(Stream,Lines) :-
	get_code(Stream,CD),
	(
	 CD == -1 ->
	 Lines = []
	;
	 ut_read_stream_line_list(Stream,Lines0),
	 (
	  CD == 10 ->
	  Lines = [[]|Lines0]
	 ;
	  (
	   Lines0 == [] ->
	   Lines = [[CD]]
	  ;
	   Lines0 = [Line0|Lines00] ->
	   Lines = [[CD|Line0]|Lines00]
	  )
	 )
	).


%
%
ut_write_stream(Stream,CDS) :-
	atom_codes(CHS,CDS),
	write(Stream,CHS).


ut_write_stream_line(Stream,Line) :-
	atom_codes(CHS,Line),
	write(Stream,CHS),
	write(Stream,'\n').


ut_write_stream_line_list(_Stream,[]).
ut_write_stream_line_list(Stream,[Line|Lines]) :-
	ut_write_stream_line(Stream,Line),
	ut_write_stream_line_list(Stream,Lines).


ut_list_union(L1,L2,L) :-
	ut_append(L1,L2,L3),
	ut_sort_rdup(L3,L).


% keeps the order on the first list
%
ut_list_intersection([],_L2,[]).
ut_list_intersection([X|L1],L2,[X|L]) :-
	ut_nth(_,L2,X),
	ut_list_intersection(L1,L2,L).
ut_list_intersection([_X|L1],L2,L) :-
	ut_list_intersection(L1,L2,L).

% useful for splitting colon separated paths, such as in
% CLASSPATH and PATH environment variables

ut_split_path([],[]).
ut_split_path(CP,CPL):-
	ut_append(Pre,[58|Post],CP),!, % colon
	atom_codes(Dir,Pre),
	CPL = [Dir|More],
	ut_split_path(Post,More).
ut_split_path(CP,[CPA]):-
	atom_codes(CPA,CP).

ut_trim(Cs0, Cs) :-
	trim_left(Cs0, Cs1),
	reverse(Cs1, Cs2),
	trim_left(Cs2, Cs3),
	reverse(Cs3, Cs).

trim_left([C|Cs], Ts) :-
	trimable_char(C),
	!,
	trim_left(Cs, Ts).
trim_left(Cs, Cs).

trimable_char(32).
trimable_char(10).
trimable_char(13).
trimable_char(44).% ,


% splits the atom B considering the atom A as a separator, and returns
% the list of atoms C
ut_split_atom(A,B,C):-
	atom_chars(A,A_Ch),
	atom_chars(B,B_Ch),
	append(B_Ch,A_Ch,BA_Ch),
	ut_split_atom_3(A_Ch,BA_Ch,ABA_Ch),
	ut_split_atom_2(A_Ch,ABA_Ch,C),
	!.


ut_split_atom_3(A_Ch,BA_Ch,NewABA_Ch):-
	append(A_Ch,ABA_Ch,BA_Ch),
	ut_split_atom_3(A_Ch,ABA_Ch,NewABA_Ch).
ut_split_atom_3(_,ABA_Ch,ABA_Ch).


ut_split_atom_2(_,[],[]).
ut_split_atom_2(X,Y,[A|O]):- 
	append(Z,X,ZX),
	append(ZX,R,Y),
	atom_chars(A,Z),
	ut_split_atom_3(X,R,NewR),
	ut_split_atom_2(X,NewR,O).




%
ut_cputime(T) :-
	statistics(runtime,[T,_]).

%
%
ut_cputime_to_runtime(T1,T2,T):-
	T is ceiling(T2-T1).
%
%
ut_cputimes_to_runtimes([],[]).
ut_cputimes_to_runtimes([(Msg,T1,T2)|CTs],[(Msg,T)|RTs]) :-
	T is ceiling(T2-T1),
	ut_cputimes_to_runtimes(CTs,RTs).


ut_file_name_ext(File,Name,Ext) :-
	atom(File),!,
	atom_codes(File,FileAsStr),
	file_name_extension_str(FileAsStr,NameAsStr,ExtAsStr),
	atom_codes(Name,NameAsStr),
	atom_codes(Ext,ExtAsStr).

ut_file_name_ext(File,Name,Ext) :-
	atom(Name),
	atom(Ext),!,
	atom_concat(Name,Ext,File).

ut_file_name_ext(File,Name,Ext) :-
	file_name_extension_str(File,Name,Ext).

file_name_extension_str(File,Name,Ext) :-
	nonvar(File),!,
	(
	    Ext = [0'.|X],
	    append(Name, Ext, File),
	    \+ member(0'., X) -> true
	;
	    Ext = [],
	    Name = File
	).

file_name_extension_str(File,Name,Ext) :-
	nonvar(Name),
	nonvar(Ext),!,
	append(Name,Ext,File).

ut_basename(FileName,BaseName) :-
	ut_file_name_ext(FileName,BaseName,_).

ut_extension(FileName,Extension) :-
	ut_file_name_ext(FileName,_,Extension).

ut_no_path_filename(P,F) :-
	atom(P),
	atom_codes(P,PasStr),!,
	no_path_filename_str(PasStr,FasStr),
	atom_codes(F,FasStr).

ut_no_path_filename(P,F) :-
	no_path_filename_str(P,F).

no_path_filename_str(P, F) :-
        append(_, [0'/|R], P), !,
        no_path_filename_str(R, F).

no_path_filename_str(F, F).

ut_print_list([]).
ut_print_list([E|More]):-
    copy_term(E,E2),
    numbervars(E2,0,_),
    format('~p~n',[E2]),
    ut_print_list(More).

ut_subseteq([],_).
ut_subseteq(_,[]):-!,fail.
ut_subseteq([X|Xs],[X|Ys]) :- !,ut_subseteq(Xs,Ys).
ut_subseteq([X|Xs],[_|Ys]) :- ut_subseteq([X|Xs],Ys).
