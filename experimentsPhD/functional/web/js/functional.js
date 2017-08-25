var systems=[
	"CoFloCo",
	"CoFloCo_max",
	"Raml"
	];


var results_dir={"CoFloCo":"../functional/cofloco_files/results/",
"CoFloCo_max":"../functional/cofloco_files/results_max/",
		 "Raml":"../functional/raml_files/results/"};

var out_extension={
"CoFloCo":".out",
"CoFloCo_max":".out",
"Raml":".out"};

var Source_dir="../functional/raml_files/examples/";
var crs_dir="../functional/cofloco_files/examples_abs/";

var systems_intern={
	"CoFloCo":"cofloco",
	"CoFloCo_max":"cofloco",
	"Raml":"raml"};


var XMLs={
"CoFloCo":"fun_results_cofloco.xml",
"CoFloCo_max":"fun_results_cofloco_max.xml",
"Raml":"fun_results_raml.xml"};

var type_bound="upper";
