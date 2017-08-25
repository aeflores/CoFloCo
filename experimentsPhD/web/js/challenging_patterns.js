var systems=[
	"Real",
	"CoFloCo",
	"PUBS",
	"Loopus",
	"KoAt"];


var results_dir={"CoFloCo":"../challenging_patterns/cofloco_files/results/",
		"PUBS":"../challenging_patterns/pubs_files/results/",
                  "Loopus":"../challenging_patterns/loopus_files/results/",
                  "KoAt":"../challenging_patterns/koat_files/results/"};

var out_extension={"CoFloCo":".ces.out",
		  "PUBS":".pubs.ces.out",
                  "Loopus":".o.out",
                  "KoAt":".koat.out"};

var Source_dir="../examples_challenging_patterns/";

var systems_intern={
		"Real":"ideal",
	"CoFloCo":"cofloco",
	"PUBS":"pubs_ub",
	"Loopus":"loopus",
	"KoAt":"koat",
	"C4b":"c4b",
	"Rank":"rank"};


var XMLs={
"Real":"ch_results_ideal.xml",
"CoFloCo":"ch_results_cofloco.xml",
"PUBS":"ch_results_pubs.xml",
"Loopus":"ch_results_loopus.xml",
"KoAt":"ch_results_koat.xml"};

var type_bound="upper";
