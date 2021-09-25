
CoFloCo
=======

CoFloCo is a static analysis tool to infer automatically symbolic complexity upper and lower bounds of imperative and recursive programs.
CoFloCo's analysis is not binded to any specific programming language, instead it takes an abstract representation of programs
as an input. The abstract representation is a set of cost equations that can be generated from source code, bytecode or
other intermediate representations.

CoFloCo is intended to be used as a backend. Here are some systems that use CoFloCo:
 * [CoFloCo+llvm2kittel](http://cofloco.se.informatik.tu-darmstadt.de/web-interface/clients/web/):
   A web interface to analyze programs written in C with the help of [llvm2kittel](https://github.com/s-falke/llvm2kittel) and [easyinterface](https://github.com/abstools/easyinterface).

 * [Saco](http://costa.ls.fi.upm.es/saco/web/): Saco contains multiple static analyses for concurrent programs written in the ABS language. 
   CoFloCo can be selected as an alternative backend to PUBS for the resource analysis.

 * [SRA](http://sra.cs.unibo.it/index.html): A resource analysis tool for a concurrent language with explicit acquire and release operations for virtual machines.


The main techniques used in CoFloCo are described in the papers:
 * [Antonio Flores-Montoya, Reiner Hähnle: Resource Analysis of Complex Programs with Cost Equations. APLAS 2014: 275-295](https://www.se.tu-darmstadt.de/fileadmin/user_upload/Group_SE/Page_Content/Group_Members/Antonio_Flores-Montoya/APLAS14techReport.pdf)
 * [Antonio Flores-Montoya: Upper and Lower Amortized Cost Bounds of Programs Expressed as Cost Relations. FM 2016](https://www.informatik.tu-darmstadt.de/fileadmin/user_upload/Group_SE/Publications/FM2016_extended.pdf) 
 * [Antonio Flores-Montoya: Cost Analysis of Programs Based on the Refinement of Cost Relations. PhD thesis](http://tuprints.ulb.tu-darmstadt.de/6746/) 

Using Docker
-------------

There is a CoFloco docker image that you can use to run CoFloCo:
```
docker pull afloresmontoya/cofloco
```

Once you have pulled the image, you can run:
```
docker run -it afloresmontoya/cofloco
```

and execute CoFloCo inside it, e.g.:
```
cofloco -i examples/testing/ex1.ces
```


Requirements:
--------------
 * Linux or Mac: In principle it should be possible to use CoFloCo in Windows but it might require some slight changes.
   
 * [SWI-Prolog](http://www.swi-prolog.org/) (Tried on Versions 6.6.6 and 7.4.2) or [YAP-Prolog](http://www.dcc.fc.up.pt/~vsc/Yap/) (Development version 6.3.3)
     
     
 * [GMP](https://gmplib.org/): The GNU Multiple Precision Arithmetic Library (It is required by SWI-Prolog)
     
     
 * [Parma Polyhedra Library (PPL)](http://bugseng.com/products/ppl): CoFloCo uses the latest version available at the moment (1.2)  


Installation
--------------

To install CoFloCo and its dependencies in your machine, you can follow the steps documented in
the docker file `Dockerfile`.


Usage information
------------------
  See the file `./USAGE.md` for a description of the parameters, input format, explanation of the outputs, etc.
  
Files:
------------------
  * `examples/`: Example input files
      - `examples/evaluation/` : A set of examples used in the evaluation of the tool
      - `examples/testing/` :Small examples to exercise different functionalities of the tool.
  * `src/`: Source files of CoFloCo
      - `src/main_cofloco.pl`: The main module
      - ...
  * `interfaces`: Scripts to generate cost relations from other languages
  * `static_binary`: Makefile to generate a statically linked binary
  * `cofloco`: main script for executing CoFloCo
  * `cofloco_yap`:  script for executing CoFloCo with YAP
  * `cofloco_mac`: script for executing CoFloCo in a MAC
  * `README`: this file
  * `USAGE`: basic instructions of how to use CoFloCo
  
Experiments:
------------------

CoFloCo has been compared to other cost analysis tools in several experimental evaluations.
The most recent evaluation can be found [here](http://aeflores.github.io/CoFloCo/experimentsPhD/).


Contact:
------------------
   antoniofloresmontoya@gmail.com

Contributors:
------------------
   * Antonio Flores-Montoya
   * Clemens Danninger (Lisp interface) 
   
Credits:
------------------
CoFloCo uses the stdlib created by the costa team (http://costa.ls.fi.upm.es/)
and was in part inspired by PUBS http://costa.ls.fi.upm.es/pubs/pubs.php.

   
