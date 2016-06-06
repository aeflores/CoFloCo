
:- module(res_polyhedra,[
		     lp_mrep_to_grep/2,
		     lp_grep_to_mrep/2,
		     lp_eliminate_vars/3,
		     lp_convexhull/3,
		     lp_maximize/5,
		     lp_add_polyhedra/3,
		     lp_is_empty/2,
		     lp_get_point/2,
		     poly_test/1
		    ]).

:- use_module(stdlib(utils),[ut_append/3,ut_length/2]).
:- use_module(stdlib(list_utils),[remove_many_lu/3,take_lu/3]). 
:- use_module(stdlib(parsing_writing),[write_biproduct/3,write_sum/2]).
:- use_module(stdlib(fraction_list), [multiply_frl/3,divide_frl/3]).
:- use_module(stdlib(pair_list),[zip_with/4]). 
:- use_module(stdlib(coefficients_sum),[coeffs_cs/3]).
:- use_module(stdlib(linear_expression), [parse_le/2]).

:- use_module(stdlib(matrix_constraint)).

:-use_module(stdlib(polyhedra_ppl)).


%% lp_mrep_to_grep(+MRep,-GRep):
%%
%%   converts from matrix to generator representation
%%
lp_mrep_to_grep(MRep,GRep) :-
	MRep = mrep(N,_),
	my_mrep_to_constraints( MRep,0,_,Vs,PPL_Cs),
	ppl_new_C_Polyhedron_from_constraints(PPL_Cs,P),
	ppl_Polyhedron_get_generators(P,PPL_Gs),
	ppl_generator_my_generators(PPL_Gs,Vs,N,GRep),
	ppl_delete_Polyhedron(P),
	!.

%% lp_grep_to_mrep(+GRep,-MRep)
%%
%%   converts from generator to matrix representation
%%
lp_grep_to_mrep(GRep,MRep) :-
	GRep = grep(N,Points,Rays),
	to_ppl_generator(N,Points,Vs,Rays,PPL_Gs),
	ppl_new_C_Polyhedron_from_generators(PPL_Gs,P),
	ppl_Polyhedron_get_constraints(P,PPL_Cs),
	constraints_to_mrep(PPL_Cs,N,Vs,MRep),
	ppl_delete_Polyhedron(P),
	!.

%% lp_eliminate_vars(+MRep,+Dims,+MRep_1):
%%
%%   eliminates the dimensions (i.e., vars) specified in Dims from the
%%   polyhedron specified by MRep.
%%
%%   +Dims can be a list of numbers indicating the dimensions to be
%%   eliminated, or a number, in which case all dimension above this
%%   number are eliminated.
%%
lp_eliminate_vars(MRep,Dims,MRep_1) :-
	Dims = [_|_],
	!,
    mrep_to_constraints( MRep, Vs, PPL_Cs), 
    remove_many_lu( Vs, Dims, Pj_Vs),
    numbervars( Pj_Vs, 0, HDim),
    numbervars( f(Vs, PPL_Cs), HDim, _),
    eliminate_vars_x( PPL_Cs, HDim, Pj_Vs, MRep_1).

%% see above.
%%
lp_eliminate_vars(MRep,Dims,MRep_1) :-
	integer(Dims),
	!,
    mrep_to_constraints(MRep,Vs,PPL_Cs),
    numbervars(Vs,0,_),     
    take_lu( Dims, Vs, PjVs),
    eliminate_vars_x( PPL_Cs, Dims, PjVs, MRep_1).

eliminate_vars_x(PPL_Cs,Dims, PjVs,MRep_1) :- 
	ppl_new_C_Polyhedron_from_constraints(PPL_Cs,P),
	ppl_Polyhedron_remove_higher_space_dimensions(P, Dims),
	ppl_Polyhedron_get_constraints(P,PPL_Cs_1),
	constraints_to_mrep(PPL_Cs_1,Dims,PjVs,MRep_1),
	ppl_delete_Polyhedron(P),
    !.



%% lp_convexhull(+MRep_1,+MRep_2,-MRep_3):
%%
%%  computes the convex hull of the polyhedra MRep_1 and MRep_2 (of
%%  the same dimension). The returned in MRep_3.
%%  
lp_convexhull(MRep_1,MRep_2,MRep_3) :-
	MRep_1 = mrep(N,_),
	MRep_2 = mrep(N,_),
    mrep_to_constraints( MRep_1, Vs, PPL_Cs_1),
    mrep_to_constraints( MRep_2, Vs, PPL_Cs_2),
    numbervars( Vs, 0, _),
	ppl_new_C_Polyhedron_from_constraints(PPL_Cs_1,P1),
	ppl_new_C_Polyhedron_from_constraints(PPL_Cs_2,P2),
	ppl_Polyhedron_upper_bound_assign(P1, P2),
	ppl_Polyhedron_get_constraints(P1,PPL_Cs_3),
	constraints_to_mrep(PPL_Cs_3,N,Vs,MRep_3),
	ppl_delete_Polyhedron(P1),
	ppl_delete_Polyhedron(P2),
	!.

%% lp_add_polyhedra(+MRep_P, +MRep_Q, -MRep_PplusQ):
%%
%%  MRep_PplusQ is a polyhedron defined as
%%
%%    MRep_P+MRep_Q = { x+y | x\in MRep_P, y\in MRep_Q }
%%
lp_add_polyhedra(MRep_P, MRep_Q, MRep_PplusQ) :-
	MRep_P = mrep(N,_),
	MRep_Q = mrep(N,_),
	N1 is N+1,
	my_mrep_to_constraints(MRep_P,N1,N2,Vs_1,PPL_Cs_Q),
	my_mrep_to_constraints(MRep_Q,N2,_ ,Vs_2,PPL_Cs_P),
	ut_length(Vs_0,N),
	numbervars(Vs_0,0,_),
	equalize(Vs_0,Vs_1,Vs_2,Cs_EQ),
	ut_append(PPL_Cs_Q,PPL_Cs_P,Cs_1),
	ut_append(Cs_EQ,Cs_1,Cs_2),
	ppl_new_C_Polyhedron_from_constraints(Cs_2,H),
	ppl_Polyhedron_remove_higher_space_dimensions(H, N),
	ppl_Polyhedron_get_constraints(H,PPL_Cs_3),
	constraints_to_mrep(PPL_Cs_3,N,Vs_0,MRep_PplusQ),
	ppl_delete_Polyhedron(H).

equalize([],[],[],[]).
equalize([Z|Zs],[X|Xs],[Y|Ys],[Z=X+Y|Es]) :-
	equalize(Zs,Xs,Ys,Es).

%% lp_maximize(+MRep,+ObjFunc,+Domain,-Status,-Point):
%%
%%   solves  linear programming problems: maximize +ObjFunc
%%   w.r.t MRep. Status can be: optimized, unbounded, or
%%   unfeasible. In case Status=optimized then Point is unified with
%%   the solution.
%%    
lp_maximize(MRep,ObjFunc,Domain,Status,Point) :-
	my_mrep_to_constraints(MRep,0,_,Vs,PPL_Cs),
	to_ppl_lexp(ObjFunc,Vs,PPL_ObjFunc),
	( Domain = int -> IntVs=Vs ; IntVs=[]),
	MRep = mrep(N,_),
	ppl_mip(PPL_Cs, N, Vs, IntVs, PPL_ObjFunc, max, Status, Point),
	!.

%% lp_is_empty(+MRep,-YesNo):
%%
lp_is_empty(MRep,YesNo) :-
	my_mrep_to_constraints(MRep,0,_,_Vs,PPL_Cs),
	ppl_new_C_Polyhedron_from_constraints(PPL_Cs,P),
	( ppl_Polyhedron_is_empty(P)
    ->  YesNo = yes
	;   YesNo = no
	),
	ppl_delete_Polyhedron(P).

%%
%%
lp_get_point(MRep,P) :-
	lp_mrep_to_grep(MRep,GRep), % just take a vertix as a solution for now
	GRep = grep(_,[P|_],_).
	     
%%
%%
ppl_mip(PPL_Cs, Dim, Vs, IntVs, PPL_ObjFunc, Mode, Status,Point) :-
	ppl_new_MIP_Problem(Dim,PPL_Cs,PPL_ObjFunc,Mode,P),
	ppl_MIP_Problem_add_to_integer_space_dimensions(P,IntVs),
	ppl_MIP_Problem_solve(P, Status),
	( Status = optimized ->
	    ppl_MIP_Problem_feasible_point(P,G),
	    ppl_point_to_point(G,Vs,Point)
	;
	    Point = none
	),
	ppl_delete_MIP_Problem(P).

%%
%  to_ppl_lexp( + Cs: list<int> , + Vs : list<?> , - E :)
%
%  builds the expression C1 * V1 + C2 * V2 + ... + Cn * Vn,
%  omitting those terms Ci*Vi where Ci = 0
%
to_ppl_lexp(Ns,Vs,E) :- write_biproduct( Ns, Vs, E). 

my_mrep_to_constraints( MRep,VNum_S,VNum_E,Vs,Cs) :-
    mrep_to_constraints(MRep,Vs,Cs),
	numbervars(Vs,VNum_S,VNum_E). 

to_ppl_generator(N, Points, Vs, Rays, PPL_Gs) :-
	ut_length(Vs,N),
	numbervars(Vs,0,_),
	to_ppl_points(Points,Vs,PPL_Gs-T),
	to_ppl_rays(Rays,Vs,T-[]).

to_ppl_points([],_,T-T).
to_ppl_points([P|Ps],Vs,[PPL_P|H]-T) :-
	to_ppl_point(P,Vs,PPL_P),
	to_ppl_points(Ps,Vs,H-T).

to_ppl_rays([],_,T-T).
to_ppl_rays([P|Ps],Vs,[PPL_P|H]-T) :-
	to_ppl_ray(P,Vs,PPL_P),
	to_ppl_rays(Ps,Vs,H-T).

to_ppl_point(P,Vs,PPL_P) :-
	get_denom(P,D),
	to_ppl_point_1(P,Vs,E),
	PPL_P = point(E,D).

to_ppl_ray(P,Vs,PPL_R) :-
	to_ppl_point_1(P,Vs,E),
	PPL_R = ray(E).


to_ppl_point_1([P],[V],P*V) :-
	integer(P),
	!.
to_ppl_point_1([P/_],[V],P*V) :-
	!.
to_ppl_point_1([P|Ps],[V|Vs],P*V+E) :-
	integer(P),
	!,
	to_ppl_point_1(Ps,Vs,E).
to_ppl_point_1([P/_|Ps],[V|Vs],P*V+E) :-
	to_ppl_point_1(Ps,Vs,E).


get_denom(Ps,D) :-
	get_denom_1(Ps,_,D).

get_denom_1([],D,D) :-
	(var(D) -> D=1 ; true).
get_denom_1([P|Ps],AD,D) :-
	integer(P),
	get_denom_1(Ps,AD,D).
get_denom_1([_/AD|Ps],AD,D) :-
	get_denom_1(Ps,AD,D).


ppl_generator_my_generators(PPL_Gs,Vs,N,Gs) :-
	pplgen_my_gens(PPL_Gs,Vs,Points,Rays),
	Gs = grep(N,Points,Rays).

pplgen_my_gens([],_Vs,[],[]).
pplgen_my_gens([X|Xs],Vs,Ps,Rs) :-
    pplgen_my_gen(X,Vs,Ps-Ps_T,Rs-Rs_T),
    pplgen_my_gens(Xs,Vs,Ps_T,Rs_T).

pplgen_my_gen( ray(E) ,Vs,Ps-Ps,[R|Rs]-Rs) :-
    lexp_to_vars_coeffs( E, Vs, R). 
pplgen_my_gen( line(E),Vs,Ps-Ps,[R1,R2|Rs]-Rs) :-
    lexp_to_vars_coeffs( E, Vs, R1),
    multiply_frl( R1, -1 , R2).
pplgen_my_gen( point(E) ,Vs,[P|Ps]-Ps,Rs-Rs) :-
    lexp_to_vars_coeffs( E, Vs, P).
pplgen_my_gen( point(E,D),Vs,[P|Ps]-Ps,Rs-Rs) :-
    lexp_to_vars_coeffs( E, Vs, P_1), 
    divide_frl( P_1, D, P). 

ppl_point_to_point( point(E) ,Vs,Point) :-
    lexp_to_vars_coeffs( E, Vs, Point).
ppl_point_to_point( point(E,D),Vs,Point) :-
    lexp_to_vars_coeffs( E, Vs, P_1), 
    divide_frl( P_1, D, Point). 


lexp_to_vars_coeffs( E, Vs, Ps) :-
    parse_le( E, Cs+0),
    coeffs_cs( Cs, Vs,Ps).



%%%
%%%
%%%




    

%%%%
%%%% TESTS
%%%%

poly_test(1) :-
	Cs = mrep(3,[[1,1,0],[1,0,1],[0,1,1],[1,1,1]] =< [2,3,4,4]),
	lp_mrep_to_grep(Cs,Gs),
	write(Gs).

poly_test(2) :-
	Gs = grep(4,[[1/2,3/2,5/2,0]],[[-1,-1,1,0],[-1,1,-1,0],[1,-1,-1,0],[0,0,0,1]]),
	lp_grep_to_mrep(Gs,Cs),
	format("~p~n",[Cs]).

poly_test(3) :-
    %  x   y
    % -x + y =< 1
    %  x     =< 0
    %
    %
	Cs = mrep(2,[[-1,-1],[1,0]] =< [1,0]),
	lp_eliminate_vars(Cs,[1],Cs_1),
	write(Cs_1).

poly_test(4) :-
	Cs_1 = mrep(1,[[1],[-1]] =< [2,-1]),
	Cs_2 = mrep(1,[[1],[-1]] =< [5,-4]),
	lp_convexhull(Cs_1,Cs_2,Cs_3),
	write(Cs_3).

poly_test(5) :-
	Cs = mrep(3,[[1,1,0],[1,0,1],[0,1,1]] =< [2,3,4]),
	lp_maximize(Cs,[1,1,1],int,S,P),
	format("~p - ~p~n",[S,P]).

poly_test(5) :-
	Cs = mrep(3,[[1,1,0],[1,0,1],[0,1,1]] =< [2,3,4]),
	lp_maximize(Cs,[1,1,1],int,S,P),
	format("~p - ~p~n",[S,P]).

poly_test(51) :-    
	Cs = mrep(3, % x y z
              [[1,1,0], % x+y <= 2
               [1,0,1], % x+z <= 3 
               [0,1,1]  % y+z <= 4
              ] =< [2,3,4]),
	lp_get_point(Cs,P),
	format("~p~n",[P]).

poly_test(6) :-
	Cs = mrep(4,[%x y w z
		     [1,1,0,0], % x+y <= 1
		     [0,1,0,1], % y+z <= 2
		     [1,0,0,1], % x+z <= 1
		     [1,0,1,0], % x+w <= 1
		     [0,1,1,0], % y+w <= 2
		     [0,0,1,1]  % x+w <= 0
		    ] =< 
		    [1,2,1,1,2,0]),
	lp_mrep_to_grep(Cs,Gs),
	format("~p~n",[Gs]).
