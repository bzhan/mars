  
# MARS: a toolchain for Modeling, Analyzing and veRifying hybrid Systems

Current version: v1.0
Validated on platform: 32/64bit-Ubuntu-Desktop-14.04/14.10 
Latest modification: on Feb 21th, 2019, by Jian Wang, SKLCS-ISCAS

Corresponding e-mail: chenms@ios.ac.cn, wangsl@ios.ac.cn

Comments and bug-reports are higly appreciated.

-----------------------------------

## Install MARS

1. Extract MARS_v1.0.tar.bz2, which should create the structure

```bash
/MARS_v1.0
/MARS_v1.0/CaseStudies/HCS
/MARS_v1.0/Sim2HCSP
/MARS_v1.0/H2S
/MARS_v1.0/HHLProver
/MARS_v1.0/QEInvGenerator
/MARS_v1.0/SOSInvGenerator
/MARS_v1.0/README.md
```


2. Install the required tools and libraries

	1. binfmt-support
	```bash
	sudo apt-get install binfmt-support
	```


	2. C++ compiler
	```bash
	sudo apt-get install g++
	```

	3. Flex and Bison
	```bash
	sudo apt-get install Flex Bison
	```

	4. JRE (installed by default in Ubuntu)

	5. Isabelle (validated in R2014)
		http://isabelle.in.tum.de/

	6. Mathematica (validated in R10)
		http://www.wolfram.com/mathematica/

	7. Matlab (validated in R2014a~R2018a, with Simulink bundled)
		http://www.mathworks.com/products/matlab/

	8. Yalmip (remember to add paths in your MATLAB path)
		http://users.isy.liu.se/johanl/yalmip/

	9. SDPT3
		http://www.math.nus.edu.sg/~mattohkc/sdpt3.html

	10. OGDF (a library for the automatic layout of diagrams, needed in the inverse translator H2S)
		http://www.ogdf.net/doku.php/tech:download

3. Set environment variables

```bash
export OGDFHOME=".../OGDF"
export MARSHOME=".../MARS_v1.0"
export MATLABHOME=".../Matlab_R2014a/bin"
export MATHEMATICAHOME=".../Mathematica10/Executables"
```

## Example: HCS

----------------------------------------

### Sim2HCSP

Go to the HCS directory:

```bash
cd $MARSHOME/CaseStudies/HCS
```

Convert the mdl file to xml file

```matlab
save_system('hcs.mdl', 'hcs.xml','ExportToXML', true) %in matlab, in case you have no hcs.xml
```

Transfer the Simulink to hcsp and correpsonding isabelle theories.

```bash
java -jar $MARSHOME/Sim2HCSP/Sim2HCSP.jar -xml hcs.xml -uds uds/
```

If you do not want to generate the HCSP result, use -compact true.

```bash
java -jar $MARSHOME/Sim2HCSP/Sim2HCSP.jar -compact true -xml hcs.xml -uds uds/
```

move the generated theory files to HCS directory:

```bash
cp proof/goal.thy proof/assertionDef.thy .
```

### HCSP -> System C

convert the hcsp to system c

```bash
java -jar $MARSHOME/HCSP2SystemC/HCSP2SystemC.jar -hcsploc system.hcsp -delta 1 -ep 1 -h 0.7 -vep 1 -T 199
```

--------------------------------------

### H2S

```bash
cp process ../../H2S/

cd ../../H2S/

./Parser < process

$MATLABHOME/matlab -nodesktop -nosplash -nojvm -r "uiopen('h2s.mdl',1)"
```

---------------------

### HHLProver + Invariant Generator

1. open $MARSHOME/CaseStudies/HCS/goal.thy in Isabelle, and click 'Yes' to load required files

2. specify the degree of invariant template, for example 6, in the pop-up terminal

The proof will be completed when you see "No subgoals!" in Isabelle.

---------------------

### An additional Mathematica notebook 

$MARSHOME/SOSInvGenerator/InvChecker.nb is provided for an intuitive graph of the generated invariant. Enjoy.

