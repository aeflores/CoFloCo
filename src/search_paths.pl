
:- dynamic user:file_search_path/2.
:- multifile user:file_search_path/2.

:- prolog_load_context(directory, Dir),
	retractall(user:file_search_path(stdlib,_)),
   (\+user:file_search_path(stdlib,_)->
   atom_concat(Dir,'/costa_stdlib/',Dir_basic),
   asserta(user:file_search_path(stdlib, Dir_basic)),
   
   atom_concat(Dir,'/costa_stdlib/collections/',Dir_collections),
   asserta(user:file_search_path(stdlib, Dir_collections)),
   
   atom_concat(Dir,'/costa_stdlib/graph_algorithms/',Dir_graph),
   asserta(user:file_search_path(stdlib, Dir_graph)),
   
   atom_concat(Dir,'/costa_stdlib/numeric_abstract_domains/',Dir_nad),
   asserta(user:file_search_path(stdlib, Dir_nad)),
   
   atom_concat(Dir,'/costa_stdlib/math/',Dir_math),
   asserta(user:file_search_path(stdlib, Dir_math)),
   
   atom_concat(Dir,'/costa_stdlib/sys_dep/swi_prolog/unix/',Dir_ppl),
   asserta(user:file_search_path(stdlib, Dir_ppl)),
   
   atom_concat(Dir,'/lib/',Dir_ppl_binary), 
   asserta(user:file_search_path(foreign, Dir_ppl_binary))
   
   ;
   true
   ).

