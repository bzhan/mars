  
# MARS: a toolchain for Modeling, Analyzing and veRifying hybrid Systems

A new version of README file is in progress.

## User interface for simulator

* Start simulator:

```
python -m ss2hcsp.server.simulator_server
```

* Start user interface (using a second terminal):

```
cd hcsp_simulator
npm start
```

(for the first time, make sure appropriate version of node.js and npm are installed,
then run ```npm install```).

* Click `Read HCSP File` button to open a file. For some simple example files, see `Examples/HCSP` folder.

## Stateflow conversion tests and examples:

* Run all tests:

```python -m unittest ss2hcsp.tests.sf_convert_test```

* Translation code at ```ss2hcsp/sf```

* Stateflow benchmarks at ```Examples/Stateflow/tests```

* RTPS case study at ```Stateflow/sf_new```


## Code for Semantics of Stateflow in Isabelle:

We define a formal operational semantics for a subset of Stateflow and formalize it in Isabelle/HOL, and we implement an automatic translator from Stateflow to Isabelle and an execution engine based on the semantics, which generates the execution results of this model according to the semantics automatically.

* To run a test, we add an example path in ```ss2hcsp/tests/sf_isabelle_test``` and run:

```python -m unittest ss2hcsp.tests.sf_isabelle_test```

then check the result at Semactic_Stateflow/example_name.thy

* Translator code at ```ss2hcsp/sf/sf_isabelle.py```

* Semantics and engine code at ```Semactic_Stateflow```

* All Stateflow examples at ```Examples/Stateflow/translate```


