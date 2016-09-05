
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

Note: only the first system uses the techniques implemented in this branch at the moment.

The main techniques used in CoFloCo are described in the papers:
 * [Antonio Flores-Montoya, Reiner Hähnle: Resource Analysis of Complex Programs with Cost Equations. APLAS 2014: 275-295](https://www.se.tu-darmstadt.de/fileadmin/user_upload/Group_SE/Page_Content/Group_Members/Antonio_Flores-Montoya/APLAS14techReport.pdf)
 * [Antonio Flores-Montoya: Upper and Lower Amortized Cost Bounds of Programs Expressed as Cost Relations. FM 2016] (https://www.informatik.tu-darmstadt.de/fileadmin/user_upload/Group_SE/Publications/FM2016_extended.pdf) 

Using Vagrant
-------------

You can use CoFloCo without installing any of the dependencies using 
[Vagrant](https://www.vagrantup.com).  Vagrant will start a
Linux virtual machine and install the needed dependencies.  In the
`CoFloCo/` directory, run the command `vagrant up` to provision and
start a VM, then `vagrant ssh` to connect.

Within the VM, this directory is accessible in the directory `/vagrant`.

Requirements:
--------------
 * Linux or Mac: In principle it should be possible to use CoFloCo in Windows but it might require some slight changes.
   
 * [SWI-Prolog](http://www.swi-prolog.org/) (Version 6.6.6) or [YAP-Prolog](http://www.dcc.fc.up.pt/~vsc/Yap/) (Development version 6.3.3)
     
     
 * [GMP](https://gmplib.org/): The GNU Multiple Precision Arithmetic Library (It is required by SWI-Prolog)
     
     
 * [Parma Polyhedra Library (PPL)](http://bugseng.com/products/ppl): CoFloCo uses the latest version available at the moment (1.2)  


Complete Installation
--------------
 * Install SWI-Prolog 6.6.6 or YAP 6.3.3 and the GMP library
 
 * CoFloCo requires the Parma Polyhedra Library (PPL) with the SWI-Prolog interface
   or YAP-Prolog installed (Depending on which prolog system you are using).
   The distributions that are available with apt-get (linux) or port (mac) do not include these 
   interfaces at the moment.

   For convenience, we included a binary of PPL for Linux x64  in  `src/lib/`. If you have this system,
   you can use CoFloCo with SWI-Prolog without compiling and installing the library. 
   Just make sure the make sure the libraries are found by cofloco before you execute it:
    
     `export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:./src/lib/`
   
   If you want to use your own installation of PPL (say you have a mac), you can download the sources from
   the official page http://bugseng.com/products/ppl/download.
   In the directory of ppl execute:
   
      `./configure --enable-interfaces=swi_prolog,yap_prolog`

      `make`

      `sudo make install`
   
	Some extra options might be necessary depending on your system. PPL provides documentation
	on how to configure and compile in different systems.
   
   
 * Once installed all the requirements, you can call CoFloCo with the script "cofloco" in the main directory: 
   
     `./cofloco -i examples/EXAMPLE_FILE`

or 
     `./cofloco_yap -i examples/EXAMPLE_FILE`


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
  * `cofloco`: main script for executing CoFloCo
  * `cofloco_yap`:  script for executing CoFloCo with YAP
  * `cofloco_mac`: script for executing CoFloCo in a MAC
  * `README`: this file
  * `USAGE`: basic instructions of how to use CoFloCo
  

Contact:
------------------
   antoniofloresmontoya@gmail.com

Contributors:
------------------
   * Antonio Flores-Montoya
   
Credits:
------------------
CoFloCo uses the stdlib created by the costa team (http://costa.ls.fi.upm.es/)
and was in part inspired by PUBS http://costa.ls.fi.upm.es/pubs/pubs.php.

CoFloCo is funded by the EU project FP7-ICT-610582 ENVISAGE: Engineering Virtualized Services 
   http://www.envisage-project.eu
   
