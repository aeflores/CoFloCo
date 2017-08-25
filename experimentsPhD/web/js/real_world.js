var systems=[
	"CoFloCo",
	"PUBS",
	"Loopus",
	"KoAt",
	"Loopus_kittel"];


var results_dir={
                "CoFloCo":"../real_world/cofloco_files/results/",
	"PUBS":"../real_world/pubs_files/results/",
                  "Loopus":"../real_world/loopus_files/results/",
                 "KoAt":"../real_world/koat_files/results/",
		  "Loopus_kittel":"../real_world/loopus+kittel_files/results/"};
var out_extension={
               "CoFloCo":".ces.out",
               		  "PUBS":".pubs.ces.out",
                  "Loopus":".out",
                  "KoAt":".koat.out",
	          "Loopus_kittel":".koat.simple.koat.c.bc.out"};

var Source_dir="../examples_c/";

var systems_intern={
	"CoFloCo":"cofloco",
	"PUBS":"pubs_ub",
	"Loopus":"loopus",
	"KoAt":"koat",
	"Loopus_kittel":"loopus_kittel"};


var XMLs={
"CoFloCo":"rw_results_cofloco.xml",
"PUBS":"rw_results_pubs.xml",
"Loopus":"rw_results_loopus.xml",
"KoAt":"rw_results_koat.xml",
"Loopus_kittel":"rw_results_loopus+kittel.xml"};

var type_bound="upper";
