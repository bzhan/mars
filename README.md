======================================================================    
MARS: a toolchain for Modeling, Analyzing and veRifying hybrid Systems

Current version: v1.0
Validated on platform: 32/64bit-Ubuntu-Desktop-14.04/14.10 
Latest modification: on Feb 9th, 2015, by Mingshuai Chen, SKLCS-ISCAS

Corresponding e-mail: chenms@ios.ac.cn, wangsl@ios.ac.cn
Comments and bug-reports are higly appreciated.
======================================================================    	


1. Extract MARS_v1.0.tar.bz2, which should create the structure

   /MARS_v1.0
   /MARS_v1.0/CaseStudies/HCS
   /MARS_v1.0/Sim2HCSP
   /MARS_v1.0/H2S
   /MARS_v1.0/HHLProver
   /MARS_v1.0/QEInvGenerator
   /MARS_v1.0/SOSInvGenerator
   /MARS_v1.0/README.md

2. Install the required tools and libraries

a. binfmt-support
	$ sudo apt-get install binfmt-support

b. C++ compiler
	$ sudo apt-get install g++

c. Flex and Bison
	$ sudo apt-get install Flex Bison

d. JRE (installed by default in Ubuntu)
	http://www.oracle.com/technetwork/java/javase/downloads/jre7-downloads-1880261.html

e. Isabelle (validated in R2014)
	http://isabelle.in.tum.de/

f. Mathematica (validated in R10)
	http://www.wolfram.com/mathematica/

g. Matlab (validated in R2012a~R2014a, with Simulink bundled)
	http://www.mathworks.com/products/matlab/

h. Yalmip (remember to add paths in your MATLAB path)
	http://users.isy.liu.se/johanl/yalmip/

i. SDPT3
	http://www.math.nus.edu.sg/~mattohkc/sdpt3.html

j. OGDF (a library for the automatic layout of diagrams, needed in the inverse translator H2S)
	http://www.ogdf.net/doku.php/tech:download

3. Set environment variables

   $ export OGDFHOME=".../OGDF"
   $ export MARSHOME=".../MARS_v1.0"
   $ export MATLABHOME=".../Matlab_R2014a/bin"
   $ export MATHEMATICAHOME=".../Mathematica10/Executables"

4. Demonstration on case study HCS

a. Sim2HCSP
		$ cd $MARSHOME/CaseStudies/HCS

		save_system('*.mdl', '*.xml','ExportToXML', true)) %in matlab, in case you have no hcs.xml

		$ $MARSHOME/Sim2HCSP/Sim2HCSP.jar -compact true -xml hcs.xml -uds uds/
java -jar $MARSHOME/Sim2HCSP/Sim2HCSP.jar -compact true -xml /home/yangg/MARS/MARS_v1.1/CaseStudies/HCS/hcs.xml -uds /home/yangg/MARS/MARS_v1.1/CaseStudies/HCS/uds/

		$ cp proof/goal.thy proof/assertionDef.thy .

b. H2S
		$ cp process ../../H2S/

		$ cd ../../H2S/

		$ ./Parser < process

		$ $MATLABHOME/matlab -nodesktop -nosplash -nojvm -r "uiopen('h2s.mdl',1)"

c. HHLProver + Invariant Generator
		open $MARSHOME/CaseStudies/HCS/goal.thy in Isabelle, and click 'Yes' to load required files

		specify the degree of invariant template, for example 6, in the pop-up terminal

d. The proof will be completed when you see "No subgoals!" in Isabelle.

e. An additional Mathematica notebook $MARSHOME/SOSInvGenerator/InvChecker.nb is provided for an intuitive graph of the generated invariant. Enjoy.

=========================================================================================================
