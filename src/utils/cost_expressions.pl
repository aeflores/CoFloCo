/** <module> cost_expressions

 This module implements the predicates that can create,
 maximize and simplify cost expressions.

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

:- module(cost_expressions,[parse_cost_expression/2,
					   cexpr_simplify/3,
					   cexpr_simplify_ctx_free/2,
					   get_asymptotic_class_name/2,
					   get_asymptotic_class/2,
					   is_linear_exp/1
					   ]).


:- use_module(cofloco_utils,[normalize_constraint/2,zip_with_op/4,write_sum/2]).
:- use_module(polyhedra_optimizations,[nad_entails_aux/3]).
:- use_module('../bound_computation/constraints_maximization',[max_min_linear_expression_all/5]).

:- use_module('../IO/params',[get_param/2]).
:- use_module(stdlib(utils),[ut_sort/2,ut_append/3,ut_member/2,ut_sort_rdup/2,ut_flat_list/2,ut_split_at_pos/4]).
:- use_module(stdlib(set_list),[remove_sl/3,union_sl/3,contains_sl/2,from_list_sl/2,difference_sl/3,insert_sl/3]).
:- use_module(stdlib(list_map),[lookup_lm/3,insert_lm/4]).

:- use_module(stdlib(numeric_abstract_domains),[nad_entails/3]).
:- use_module(stdlib(linear_expression), [parse_le/2,multiply_le/3,write_le/2]).





%! normalize_le(+Le:linear_expression,-Le_n:linear_expression) is det
% normalize the linear expression Le
normalize_le(Le,Le_n):-
	parse_le( Le, Le_x),
	write_le(Le_x,Le_n).



	
	
%! parse_cost_expression(+C:cost_expression, -C2:cost_expression) is semidet
% This predicate fails is the cost expression C does not have a valid format.
% Otherwise, it return a simplified version of C.
 parse_cost_expression(C, C2):-
	 (cexpr_simplify_ctx_free(C, C2)->
	 	true
	 ;
	 	numbervars(C,0,_),
	    throw(invalid_cost_expression(C))
	  ).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! cexpr_simplify(+Expr:cost_expression,+Cs:polyhedron,-Expr_simple:cost_expression) is det
% simplify Ls completely according to Cs.
% the result is returned in LsM.
cexpr_simplify(Expr,Cs,Expr_simple):-
	cexpr_simplify_N(Expr,-1,Cs,Expr_simple),!.


%! cexpr_simplify_ctx_free(+Expr:cost_expression,-Expr_simple:cost_expression) is det
% simplify Ls without assuming any environment.
% the result is returned in LsM.
%
% It simplifies only the outmost level (without traversing the whole cost expression)
cexpr_simplify_ctx_free(Expr,Expr_simple):-
	cexpr_simplify_N(Expr,1,[],Expr_simple).
	
%! cexpr_simplify_aux(+Cs:polyhedron,+Cost:cost_expression,-Cost_simple:cost_expression) is det
% simplify Cost completely according to Cs.
% the result is returned in Cost_simple.
%
% This predicate has an alternative order of the arguments so it can be called with maplist
% for a list of cost expressions.
cexpr_simplify_aux(Cs,Expr,Expr_simple):-
	cexpr_simplify(Expr,Cs,Expr_simple).

%! cexpr_simplify_N(+Cs:polyhedron,+N:int,+Ls:cost_expression,-LsM:cost_expression) is det
% simplify N levels of Ls according to Cs.
% If N is negative, the cost expression is completely simplified.
% the result is returned in LsM.
cexpr_simplify_N(V,0,_,V):-!.

cexpr_simplify_N(V,_,_,V):-
 	var(V),!.
cexpr_simplify_N(inf,_,_,inf).

cexpr_simplify_N(V,_,_,V):-
 	number(V),!.
cexpr_simplify_N(c(Cost_center),_,_,c(Cost_center)):-!.
 	
cexpr_simplify_N(nat(E),N,Cs,Res):-
	\+var(E),
	E=nat(E2),!,
 	cexpr_simplify_N(nat(E2),N,Cs,Res). 	
 
cexpr_simplify_N(nat(E),N,Cs,Res):-
	N1 is N-1,
 	cexpr_simplify_N(E,N1,Cs,ES),
	
 	(number(ES)->
 	  (ES>0 ->
 	   Res=ES
 	  ;
 	   Res=0
 	  )
 	;
 	 (ES==inf->
 	   Res=inf
 	 ;
	  (is_linear_exp(ES)->
	     term_variables((Cs,ES),Vars),
	     (nad_entails_aux(Vars,Cs,[ES>=0])->
	      Res=ES
	     ;
	      
	     (nad_entails_aux(Vars,Cs,[ES=<0])->
	      Res=0
	      ;
	      Res=nat(ES)
	     )
	     )
	  ;
	  
 	 Res=nat(ES)
	  )
 	 )
 	).
cexpr_simplify_N(E/D,N,Cs,ES/D):-
	N1 is N-1,
	number(D),
 	cexpr_simplify_N(E,N1,Cs,ES).

%cexpr_simplify_N(-(-E),N,Cs,ES):-!,
%	N1 is N-1,
% 	cexpr_simplify_N(E,N1,Cs,ES).
cexpr_simplify_N(-E,N,Cs,-ES):-!,
	N1 is N-1,
 	cexpr_simplify_N(E,N1,Cs,ES).

cexpr_simplify_N(min(Ls),N,Cs,Res):-!,
	N1 is N-1,
 	cexpr_simplify_min(Ls,N1,Cs,LsS),
 	(LsS=[Res]->true;
 	 Res=min(LsS)).
cexpr_simplify_N(max(Ls),N,Cs,Res):-!,
	N1 is N-1,
 	cexpr_simplify_max(Ls,N1,Cs,LsS),
 	(LsS=[Res]->true;
 	 Res=max(LsS)).
 	 
cexpr_simplify_N(Linear_exp,_,_,Res):-    
 	is_linear_exp(Linear_exp),!,
 	compress_arithmetic(Linear_exp,Res).
 	 
cexpr_simplify_N(L+R,N,Cs,Res):-!,
	%we know that L+R is not a linear expression
	N1 is N-1,
 	cexpr_simplify_N(L,N1,Cs,LS),
 	cexpr_simplify_N(R,N1,Cs,RS),
    %If N1 is zero, we don't have to check again
 	((N1 \== 0,is_linear_exp(LS+RS))->
 	 compress_arithmetic(LS+RS,Res)
 	;
	((LS==inf; RS==inf)->
	   Res=inf
	;
 	(LS==0 ->
 	    Res=RS
 	;
 	 (RS==0->
 	  Res=LS;
 	  (LS@>RS->
 	  Res=LS+RS;
 	  Res=RS+LS)
	
 	 )
 	)
	)
 	).

cexpr_simplify_N(L-R,N,Cs,Res):-!,
    %we know that L+R is not a linear expression
	N1 is N-1,
 	cexpr_simplify_N(L,N1,Cs,LS),
 	cexpr_simplify_N((-1*R),N1,Cs,RS),
 	 %If N1 is zero, we don't have to check again
 	((N1 \== 0,is_linear_exp(LS+RS))->
 	 compress_arithmetic(LS+RS,Res)
 	;
 	(LS==0 ->
 	    Res=RS
 	;
 	 (RS==0->
 	  Res=LS;
 	  (LS@>RS->
 	  Res=LS+RS;
 	  Res=RS+LS)
	
 	 )
 	)
 	).

cexpr_simplify_N(L*R,N,Cs,Res):-
	 N1 is N-1,
	 L==(-1),
	 \+var(R),!,
	 change_sign(R,RS),
	 cexpr_simplify_N(RS,N1,Cs,Res).
cexpr_simplify_N(L*R,N,Cs,Res):-
	 N1 is N-1,
	 R==(-1),
	 \+var(L),!,
	 change_sign(L,LS),
	 cexpr_simplify_N(LS,N1,Cs,Res).

cexpr_simplify_N(L*R,N,Cs,Res):-!,
	N1 is N-1,
	 %we know that L+R is not a linear expression
 	cexpr_simplify_N(L,N1,Cs,LS),
 	cexpr_simplify_N(R,N1,Cs,RS),
 	%If N1 is zero, we don't have to check again
	((N1 \== 0,is_linear_exp(LS*RS))->
 	 compress_arithmetic(LS*RS,Res)
 	;
 	( (LS==0;RS==0) ->
 	    Res=0
 	;
	  ((LS==inf;RS==inf) ->
	     Res=inf
	   ;
 	  (LS==1 ->
 	    Res=RS
 	;
 	 (RS==1->
 	  Res=LS;
 	  (LS@>RS->
 	  Res=LS*RS;
 	  Res=RS*LS)

 	   )
 	)
 	)
	)
 	).

%! cexpr_simplify_aux(+Cs:polyhedron,+N:int,+Ls:cost_expression,-LsM:cost_expression) is det
% simplify N levels of Ls according to Cs.
% If N is negative, the cost expression is completely simplified.
% the result is returned in LsM.
%
% This predicate has an alternative order of the arguments so it can be called with maplist
% for a list of cost expressions.
cexpr_simplify_aux(Cs,N,Ls,LsM):-
	cexpr_simplify_N(Ls,N,Cs,LsM).	

compress_arithmetic(E,ES):-
	normalize_le(E,ES).

%! cexpr_simplify_min(+List:list(cost_expression),+N:int,+Cs:polyhedron,-List_simpl:list(cost_expression)) is det
% simplify a list of cost expressions N levels according to Cs
% and remove redundant expressions knowing that we want to obtain the minimum.
cexpr_simplify_min(List,0,_Cs,List):-!.

cexpr_simplify_min(List,N,Cs,List_simpl):-
 	maplist(cexpr_simplify_aux(Cs,N),List,List_1),
 	%take numbers and symbolic expressions apart
 	partition(number,List_1,Ns,Vs),
 	%remove duplicates in symbolic expressions
 	from_list_sl(Vs,Vs_1),
 	%if we have at least 2 elements and inf, we can remove inf
	((contains_sl(Vs_1,inf),Vs_1=[_,_|_])->
            remove_sl(Vs_1,inf,Vs_2)
	;
	    Vs_2=Vs_1
	),
	%if there are no numbers, search for redundancies in the symbolic expressions
 	(Ns=[] ->
	   simplify_redundant(Vs_2,Cs,>=,List_simpl)
 	;
 	%otherwise, get the minimum number and consider it together with the symbolic expressions
 	min_list(Ns,N_min),
%now the non-negativeness is not implicit
% 	(N_min>0 ->
	  simplify_redundant([N_min|Vs_2],Cs,>=,List_simpl)
%	  ;
%	  % the elements in min have to be non-negative implicitly
%	  List_simpl=[0]
% 	)
 	).
 	
%! cexpr_simplify_max(+List:list(cost_expression),+N:int,+Cs:polyhedron,-List_simpl:list(cost_expression)) is det
% simplify a list of cost expressions N levels according to Cs
% and remove redundant expressions knowing that we want to obtain the maximum. 	
cexpr_simplify_max(List,0,_Cs,List):-!. 	
cexpr_simplify_max(List,N,Cs,List_simpl):-
	maplist(cexpr_simplify_aux(Cs,N),List,List_1),
	%take numbers and symbolic expressions apart
 	partition(number,List_1,Ns,Vs),
 	from_list_sl(Vs,Vs_1),
 	%if we have inf, the result is inf
 	(contains_sl(Vs_1,inf)->
 	  List_simpl=[inf]
 	;
 	%otherwise, get the maximum number
  	 (max_list(Ns,N_max)->
	    simplify_redundant([N_max|Vs_1],Cs,=<,List_simpl)
	 ;
	 (Vs_1=[]->
	 	throw(error('there is a max with no elements inside'))
	 	;
	 	simplify_redundant(Vs_1,Cs,=<,List_simpl)
	 )
	)
 	).


 
change_sign(Var,-Var):-var(Var),!.
change_sign(Constant,Neg_Cons):-
	number(Constant),!,
	Neg_Cons is -Constant.
change_sign(min(Ls),-min(Ls)).
change_sign(max(Ls),-max(Ls)).
change_sign(nat(Ls),-nat(Ls)).
change_sign(L+R,LS+RS):-
	change_sign(L,LS),
	change_sign(R,RS).

change_sign(L*R,LS*R):-
	change_sign(L,LS).
change_sign(L/R,LS/R):-
	change_sign(L,LS). 
 	
%! simplify_redundant(+Es:list(cost_expression),+Cs:polyhedron,+Op:operator,-List_simpl:list(cost_expression)) is det 	
% try to remove the redundant elements of Es according to the polyhedron Cs and the order Op.
% It compares the elements of Es and removes the ones that are guaranteed to be greater or smaller (according to Op) than others.
simplify_redundant([E|Es],Cs,Op,List_simpl):-
	partition(is_linear_exp,[E|Es],Linear,Non_linear),
	(Linear=[Lin1|Lins]->
	  simplify_redundant_1(Lins,[Lin1],Cs,Op,List_simpl_linear)
	;
	  List_simpl_linear=[]
	),
	append(List_simpl_linear,Non_linear,List_simpl).
	 

simplify_redundant_1([],Candidates,_Cs,_Op,Candidates).
simplify_redundant_1([E|Es],Candidates,Cs,Op,ListSimpl):-
	%compare the element E with the current candidates and keep the ones that are not redundant (from Candidates and E)
	check_candidates(Candidates,E,Cs,Op,[],New_candidates),
	simplify_redundant_1(Es,New_candidates,Cs,Op,ListSimpl).

% E could not be discarded by any of the candidates
check_candidates([],E,_Cs,_Op,New_candidates,[E|New_candidates]).

% E is redundant with respect to C, so we discard E
check_candidates([C|More],E,Cs,Op,Accum,New_candidates):-
	Constr=..[Op,E,C],
	term_variables((Cs,Constr),Vars),
	nad_entails_aux(Vars,Cs,[Constr]),!,
	append([C|More],Accum,New_candidates).
% C is redundant with respect to E, so we discard C and keep checking
check_candidates([C|More],E,Cs,Op,Accum,New_candidates):-
	Constr=..[Op,C,E],
	term_variables((Cs,Constr),Vars),
	nad_entails_aux(Vars,Cs,[Constr]),!,
	check_candidates(More,E,Cs,Op,Accum,New_candidates).
% we cannot prove anything about C and E
check_candidates([C|More],E,Cs,Op,Accum,New_candidates):-
	check_candidates(More,E,Cs,Op,[C|Accum],New_candidates).

  	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 
%! get_asymptotic_class_name(+Exp:cost_expression,-Name:term) is det
% given a cost expression, obtain its complexity(constant,n,n^2,n^3...infinity)
get_asymptotic_class_name(Exp,Name):-
	get_asymptotic_class(Exp,Class),
	get_class_name(Class,Name).

get_class_name(inf,infinity):-!.
get_class_name(0,constant):-!.
get_class_name(1,n):-!.
get_class_name(N,n^N).	

%! get_asymptotic_class(+Exp:cost_expression,-N:int) is det
% given a cost expression, it obtains a number that represents its complexity 
%  * constant=0
%  * n=1
%  * n^2=2
%  * n^3=3  
%  * ... 
%  * infinity=inf
get_asymptotic_class(Var,1):-
	var(Var),!.

get_asymptotic_class(inf,inf):-!.

get_asymptotic_class(Const,0):-
	ground(Const),!.
get_asymptotic_class(E,1):-
	is_linear_exp(E),!.


get_asymptotic_class(nat(E),Class):-
	get_asymptotic_class(E,Class).

get_asymptotic_class(E/_,Class):-
	get_asymptotic_class(E,Class).

get_asymptotic_class(-E,Class):-!,
 	get_asymptotic_class(E,Class).

get_asymptotic_class(min(Ls),Class):-!,
	maplist(get_asymptotic_class,Ls,Classes),
	foldl(min_class,Classes,inf,Class).
 
get_asymptotic_class(max(Ls),Class):-!,
	maplist(get_asymptotic_class,Ls,Classes),
	foldl(max_class,Classes,0,Class).

get_asymptotic_class(L+R,Class):-!,
	get_asymptotic_class(L,L_class),
	get_asymptotic_class(R,R_class),
	max_class(L_class,R_class,Class).
get_asymptotic_class(L-R,Class):-!,
	get_asymptotic_class(L,L_class),
	get_asymptotic_class(R,R_class),
	max_class(L_class,R_class,Class).

get_asymptotic_class(L*R,Class):-
 	get_asymptotic_class(L,L_class),
	get_asymptotic_class(R,R_class),
	add_class(L_class,R_class,Class).

min_class(inf,X,X):-!.
min_class(X,inf,X):-!.
min_class(N1,N2,N3):-
	N3 is min(N1,N2).
max_class(inf,_,inf):-!.
max_class(_,inf,inf):-!.
max_class(N1,N2,N3):-
	N3 is max(N1,N2).
add_class(inf,_X,inf):-!.
add_class(_X,inf,inf):-!.
add_class(N1,N2,N3):-
	N3 is N1+N2.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! is_linear_exp(Exp:cost_expression) is semidet
% It succeeds if Exp is a linear cost expression.
 is_linear_exp(V):-
 	var(V),!.
 is_linear_exp(C):-
 	number(C),!.
 is_linear_exp(-A):-!,
 	is_linear_exp(A).
 is_linear_exp(A+B):-!,
 	is_linear_exp(A),
 	is_linear_exp(B).
 is_linear_exp(A-B):-!,
 	is_linear_exp(A),
 	is_linear_exp(B).
 is_linear_exp(A*B):-!,
 	
    (ground(A);ground(B)),
 	is_linear_exp(A),
 	is_linear_exp(B).
 	
 is_linear_exp(A/B):-!,
    ground(B),
 	is_linear_exp(A),
 	is_linear_exp(B).
