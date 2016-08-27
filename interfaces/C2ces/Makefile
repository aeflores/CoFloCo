static_all:  static_cfg2ces static_koat2cfg

static_cfg2ces: cfg2ces_bin
	swipl-ld -ld-options,-static,-s -L/usr/local/lib/ppl -lppl_swiprolog -L/usr/local/lib -lppl -lgmpxx -lgmp -ltermcap -ldl -cc gcc -c++ g++ -ld g++ -pl-options,-T0,-L0,-G0,-O,-q  -o cfg2ces_static swi_executable.c cfg2ces_bin.pl
	@chmod gou+x cfg2ces_static

static_koat2cfg: koat2cfg_bin
	swipl-ld -ld-options,-static,-s -L/usr/local/lib/ppl -lppl_swiprolog -L/usr/local/lib -lppl -lgmpxx -lgmp -ltermcap -ldl -cc gcc -c++ g++ -ld g++ -pl-options,-T0,-L0,-G0,-O,-q  -o koat2cfg_static swi_executable.c koat2cfg_bin.pl
	@chmod gou+x koat2cfg_static


 cfg2ces_bin:
	@echo "" > cfg2ces_bin.pl
	@echo ":- nb_setval(compiled, true)." >> cfg2ces_bin.pl
	@echo ":- use_module('src/cfg2ces_module')." >> cfg2ces_bin.pl
	@echo "" >>  cfg2ces_bin.pl
	@echo "main :-b_setval(compiled, true),cfg2ces_module:main_bin_cfg2ces." >>  cfg2ces_bin.pl
 
 koat2cfg_bin:
	@echo "" > koat2cfg_bin.pl
	@echo ":- nb_setval(compiled, true)." >> koat2cfg_bin.pl
	@echo ":- use_module('src/koat2cfg_module')." >> koat2cfg_bin.pl
	@echo "" >>  koat2cfg_bin.pl
	@echo "main :-b_setval(compiled, true),koat2cfg_module:main_bin_koat2cfg." >>  koat2cfg_bin.pl


clean:
	@rm cfg2ces_bin.pl cfg2ces_static
	@rm koat2cfg_bin.pl koat2cfg_static
