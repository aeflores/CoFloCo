var systems=[
	"CoFloCo",
	"PUBS",
	"Loopus",
	"KoAt",
	"C4b",
	"Rank"];


var results_dir={"CoFloCo":"../upper_bounds/cofloco_files/results/",
		"PUBS":"../upper_bounds/pubs_files/results/",
                  "Loopus":"../upper_bounds/loopus_files/results/",
                  "KoAt":"../upper_bounds/koat_files/results/",
		  "C4b":"../upper_bounds/C4b_files/results/",
		  "Rank":"../upper_bounds/rank_files/results/"};

var out_extension={"CoFloCo":".ces.out",
		  "PUBS":".pubs.ces.out",
                  "Loopus":".o.out",
                  "KoAt":".koat.out",
	          "C4b":".out",
	          "Rank":".out"};

var Source_dir="../examples_literature/";

var systems_intern={
	"CoFloCo":"cofloco",
	"PUBS":"pubs_ub",
	"Loopus":"loopus",
	"KoAt":"koat",
	"C4b":"c4b",
	"Rank":"rank"};


var XMLs={
"CoFloCo":"ub_results_cofloco.xml",
"PUBS":"ub_results_pubs.xml",
"Loopus":"ub_results_loopus.xml",
"KoAt":"ub_results_koat.xml",
"C4b":"ub_results_c4b.xml",
"Rank":"ub_results_rank.xml",};

var type_bound="upper";
