### **This repository can be downloaded by the following commands:** ###

```
    $ mkdir /path/to/your/project
    $ cd /path/to/your/project
    $ git init
    $ git remote add origin git@github.com:liangdzou/Sim2HCSP.git
    $ git pull origin master
```

### **File struct:** ###

* HHLProver: A theory prover for HCSP.
* Sim2HCSP: A tool translating Simulink/Stateflow diagrams into HCSP process.
* casestudies: Including two case studies, i.e. Chinese Train Control Systems and HCS.
* casestudies/\*/\*.mdl(xml): Simulink model for the case study. (including the xml format.) 
* casestudies/\*/proof/: The interactive proof we have done for the CTCS case study.


### **Settings for Sim2HCSP:** ###

1. Install Java JRE because *Sim2HCSP* is implemented in Java.
2. Set the following environment variables, so *Sim2HCSP* can invoke *Isabelle* and import *HHLProver* automatically.

```
export IsarHOME=".../Isabelle2013"
export HCSPHOME=".../HHLProver"
```

### **Run Sim2HCSP with the following command:** ###
In Ubuntu, install "binfmt-support" and then an executable jar file can be executed directly.

```
$ In MATLAB, save_system('*.mdl', '*.xml','ExportToXML', true)
$ Sim2HCSP [-compact true] -xml *.xml -uds uds/
```

### **How to check the proof:** ###

1. Replace *thy* files with files in proof. (replace those files which are generated automatically.)
2. Check it in *Isabelle*.
