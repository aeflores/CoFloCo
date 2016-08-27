
static: cofloco_pl
	swipl-ld -ld-options,-static,-s -L/usr/local/lib/ppl -lppl_swiprolog -L/usr/local/lib -lppl -lgmpxx -lgmp -ltermcap -ldl -cc gcc -c++ g++ -ld g++ -pl-options,-T0,-L0,-G0,-O,-q  -o cofloco_static swi_executable.c cofloco_bin.pl
	@chmod gou+x cofloco_static


 cofloco_pl:
	@echo "" > cofloco_bin.pl
	##@echo ":-set_prolog_flag(verbose, silent). " > cofloco_bin.pl
	#@echo ":-initialization main." >> cofloco_bin.pl
	
	@echo ":- nb_setval(compiled, true)." >> cofloco_bin.pl
	@echo ":- use_module('../src/main_cofloco')." >> cofloco_bin.pl
	@echo "" >>  cofloco_bin.pl
	@echo "x :- member(1,[1])." >>  cofloco_bin.pl
	@echo "main :-x,b_setval(compiled, true),main_cofloco:cofloco_bin_main." >>  cofloco_bin.pl


clean:
	@rm cofloco_bin.pl cofloco_static
