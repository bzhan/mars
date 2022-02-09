  
# Code for Semantics of Stateflow in Isabelle:

## Usage
* To run a test, we enter into the root and add an example path in ```Semantic_Stateflow/sf_isabelle_test.py``` and run:

```python -m unittest Semantic_Stateflow.sf_isabelle_test```

then check the result in ```Semactic_Stateflow/example_name.thy```

## Introduction to the Files

### Syntax_Final.thy and Semantics_Final.thy
* Syntax_Final.thy: the syntax for a subset of Stateflow
* Semantics_Final.thy: the big-step operational semantics of the Stateflow subset.

### Final_ML.thy
* The tactic for the automatic execution of the Stateflow semantics.

### sf_isabelle.py and sf_isabelle_test.py
* sf_isabelle.py: a translation tool from Stateflow charts to Isabelle representations.
* sf_isabelle_test.py: the corresponding test code of the translation tool.

### example_xml
* All Stateflow examples in xls format and xml format

### example_thy
* All test Stateflow examples in .thy format


