
CoFloCo
=======

CoFloCo is a static analysis tool to infer automatically symbolic complexity bounds of imperative and recursive programs.
CoFloCo's analysis is not binded to any specific programming language, instead it takes an abstract representation of programs
as an input. The abstract representation is a set of cost equations that can be generated from source code, bytecode or
other intermediate representations.

The main techniques used in CoFloCo are described in the paper:
 * [Antonio Flores-Montoya, Reiner Hähnle: Resource Analysis of Complex Programs with Cost Equations. APLAS 2014: 275-295]
https://www.se.tu-darmstadt.de/fileadmin/user_upload/Group_SE/Page_Content/Group_Members/Antonio_Flores-Montoya/APLAS14techReport.pdf

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
   
 * [SWI-Prolog](http://www.swi-prolog.org/):  CoFloCo works with Version 6.6.6
     
     
 * [GMP](https://gmplib.org/): The GNU Multiple Precision Arithmetic Library (It is required by SWI-Prolog)
     
     
 * [Parma Polyhedra Library (PPL)](http://bugseng.com/products/ppl): CoFloCo uses the latest version available at the moment (1.1)  


Complete Installation
--------------
 * Install SWI-Prolog 6.6.6 and the GMP library
 
 * CoFloCo requires the Parma Polyhedra Library (PPL) with the SWI-Prolog interface installed.
   The distributions that are available with apt-get (linux) or port (mac) do not include the SWI-prolog
   interface at the moment.

   For convenience, we included a binary of PPL for Linux x64  in  `src/lib/`. If you have this system,
   you can avoid compiling and installing the library. 
   Just make sure the make sure the libraries are found by cofloco before you execute it:
    
     `export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:./src/lib/`
   
   If you want to use your own installation of PPL (say you have a mac), you can download the sources from
   the official page http://bugseng.com/products/ppl/download.
   In the directory of ppl execute:
   
      `./configure --enable-interfaces=swi_prolog
      make
      sudo make install`
   
	Some extra options might be necessary depending on your system. PPL provides documentation
	on how to configure and compile in different systems.
   
   
 * Once installed all the requirements, you can call CoFloCo with the script "cofloco" in the main directory: 
   
     `./cofloco -i examples/EXAMPLE_FILE`


Usage information
------------------
  See the file `./USAGE` for a description of the parameters, input format, explanation of the outputs, etc.
  
Files:
------------------
  * `examples/`: Example input files
      - `examples/evaluation/` : A set of examples used in the evaluation of the tool
      - `examples/testing/` :Small examples to exercise different functionalities of the tool.
  * `src/`: Source files of CoFloCo
      - `src/main_cofloco.pl`: The main module
      - ...
  * `cofloco`: main script for executing CoFloCo
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
   
