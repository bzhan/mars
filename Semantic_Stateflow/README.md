  
# Code for Semantics of Stateflow in Isabelle:

## Usage
* To run a test, we enter into the root and add an example path in ```Semantic_Stateflow/sf_isabelle_test.py``` and run:

```python -m unittest Semantic_Stateflow.sf_isabelle_test```

then check the result in ```Semactic_Stateflow/example_name.thy```

## Introduction to the Files

### Syntax_Final.thy and Semantics_Final.thy
* Syntax_Final.thy is the syntax for a subset of Stateflow
* Semantics_Final.thy is the corresponding semantics

### Final_ML.thy
* An execution engine based on the semantics, which generates the execution results of this model according to the semantics automatically.

### sf_isabelle.py and sf_isabelle_test.py
* sf_isabelle.py is an automatic translator from Stateflow to Isabelle
* sf_isabelle_test.py is the corresponding test code with a xml file

### example_xml
* all Stateflow examples in xls format and xml format

### example_thy
* all examples in thy format


