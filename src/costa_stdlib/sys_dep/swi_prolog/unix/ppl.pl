/* Loader for the SWI-Prolog interface.
   Copyright (C) 2001-2010 Roberto Bagnara <bagnara@cs.unipr.it>

This file is part of the Parma Polyhedra Library (PPL).

The PPL is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the
Free Software Foundation; either version 3 of the License, or (at your
option) any later version.

The PPL is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software Foundation,
Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02111-1307, USA.

For the most up-to-date information see the Parma Polyhedra Library
site: http://www.cs.unipr.it/ppl/ . */



% Export only the neccesary predicates as some others give problems in some
% versions of the ppl
:- module(ppl,
[
	 ppl_initialize/0, 
     ppl_Polyhedron_remove_higher_space_dimensions/2, 
     ppl_Polyhedron_upper_bound_assign/2,
     ppl_Polyhedron_H79_widening_assign/2,
     ppl_Polyhedron_contains_Polyhedron/2,  
     ppl_Polyhedron_is_empty/1,
     ppl_Polyhedron_minimize/5,
     ppl_Polyhedron_add_constraints/2,
     ppl_Polyhedron_maximize/5,
     ppl_new_C_Polyhedron_from_constraints/2,
     ppl_new_C_Polyhedron_from_space_dimension/3,
     ppl_Polyhedron_get_constraints/2,
 	 ppl_Polyhedron_get_minimized_constraints/2,
     ppl_Polyhedron_get_generators/2,			   
     ppl_delete_Polyhedron/1,
     ppl_Polyhedron_intersection_assign/2, 
     ppl_Polyhedron_difference_assign/2,
     ppl_Polyhedron_equals_Polyhedron/2, 
	 ppl_Polyhedron_add_space_dimensions_and_embed/2,
	 ppl_Polyhedron_remove_space_dimensions/2,
	 ppl_new_C_Polyhedron_from_C_Polyhedron/2,
 
 	 ppl_termination_test_MS_C_Polyhedron/1,
 	 ppl_termination_test_PR_C_Polyhedron/1,
 	 ppl_one_affine_ranking_function_MS_C_Polyhedron/2,
 	 ppl_one_affine_ranking_function_PR_C_Polyhedron/2,
 	 ppl_all_affine_ranking_functions_MS_C_Polyhedron/2,
 	 ppl_all_affine_ranking_functions_PR_C_Polyhedron/2,
 	  
 	  
 	 ppl_Pointset_Powerset_C_Polyhedron_remove_higher_space_dimensions/2,
 	 ppl_Pointset_Powerset_C_Polyhedron_upper_bound_assign/2,
 	 ppl_Pointset_Powerset_C_Polyhedron_BHZ03_H79_H79_widening_assign/2,    
     ppl_delete_Pointset_Powerset_C_Polyhedron/1,
     ppl_Pointset_Powerset_C_Polyhedron_geometrically_covers_Pointset_Powerset_C_Polyhedron/2,
     ppl_Pointset_Powerset_C_Polyhedron_is_empty/1,
     ppl_Pointset_Powerset_C_Polyhedron_minimize/5,
     ppl_Pointset_Powerset_C_Polyhedron_add_constraints/2,
 	 ppl_Pointset_Powerset_C_Polyhedron_maximize/5,
     ppl_new_NNC_Polyhedron_from_constraints/2,   
     ppl_new_NNC_Polyhedron_from_space_dimension/3,
     ppl_new_Pointset_Powerset_C_Polyhedron_from_space_dimension/3,
     ppl_Pointset_Powerset_C_Polyhedron_pairwise_reduce/1,
     ppl_Pointset_Powerset_C_Polyhedron_omega_reduce/1,
     ppl_Pointset_Powerset_C_Polyhedron_add_disjunct/2,
     ppl_Pointset_Powerset_C_Polyhedron_size/2,
     ppl_Pointset_Powerset_C_Polyhedron_begin_iterator/2,
     ppl_delete_Pointset_Powerset_C_Polyhedron_iterator/1,
     ppl_Pointset_Powerset_C_Polyhedron_get_disjunct/2,
     ppl_Pointset_Powerset_C_Polyhedron_increment_iterator/1,
     ppl_delete_Pointset_Powerset_C_Polyhedron/1, 
     ppl_Pointset_Powerset_C_Polyhedron_intersection_assign/2,
     ppl_Pointset_Powerset_C_Polyhedron_difference_assign/2,
     ppl_Pointset_Powerset_C_Polyhedron_geometrically_equals_Pointset_Powerset_C_Polyhedron/2,
  
   	 ppl_new_Octagonal_Shape_mpz_class_from_C_Polyhedron/2,
	 ppl_new_Octagonal_Shape_mpz_class_from_constraints/2,
	 ppl_new_Octagonal_Shape_mpz_class_from_space_dimension/3,
	 ppl_Octagonal_Shape_mpz_class_add_constraints/2,
     ppl_Octagonal_Shape_mpz_class_remove_higher_space_dimensions/2,
     ppl_Octagonal_Shape_mpz_class_BHMZ05_widening_assign/2,
     ppl_Octagonal_Shape_mpz_class_contains_Octagonal_Shape_mpz_class/2,     
     ppl_Octagonal_Shape_mpz_class_intersection_assign/2,
	 ppl_Octagonal_Shape_mpz_class_upper_bound_assign/2,  
     ppl_Octagonal_Shape_mpz_class_is_empty/1, 
     ppl_Octagonal_Shape_mpz_class_get_constraints/2,
 	 ppl_Octagonal_Shape_mpz_class_get_minimized_constraints/2,	    
     ppl_delete_Octagonal_Shape_mpz_class/1,
     ppl_new_Octagonal_Shape_mpz_class_from_Octagonal_Shape_mpz_class/2,
     ppl_Octagonal_Shape_mpz_class_add_space_dimensions_and_embed/2,
     ppl_Octagonal_Shape_mpz_class_remove_space_dimensions/2	 
]).


:- load_foreign_library(foreign('libppl_swiprolog.so')).
