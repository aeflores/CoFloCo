var systems=[
	"CoFloCo",
//	"CoFloCo_old",
	"PUBS"];


var results_dir={"CoFloCo":"../trs_evaluation/cofloco_files/results/",
		"PUBS":"../trs_evaluation/pubs_files/results/"};

var out_extension={"CoFloCo":".ces.out",
		  "PUBS":".pubs.ces.out"};

var Source_dir="../trs_evaluation/cofloco_files/examples/";
var Source_ending=".ces";
var systems_intern={
	"CoFloCo":"cofloco",
	"PUBS":"pubs_ub"};


var XMLs={
"CoFloCo":"trs_results_cofloco.xml",
"PUBS":"trs_results_pubs.xml"};

var type_bound="upper";
