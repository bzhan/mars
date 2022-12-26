  
# Code for Semantics of Stateflow in Isabelle:

## Usage
* To run a test, we enter into the root and add an example path in ```Semantic_Stateflow/sf_isabelle_test.py``` and run:

```python3 -m unittest Semantic_Stateflow.sf_isabelle_test```

then check the result in ```Semactic_Stateflow/example_name.thy```

* Except the example xml file, you can provide the input event, the iterations of the chart and the outputs you want to get as a json file like ```Semantic_Stateflow/info.json```, And after that you can add the json path in ```Semantic_Stateflow/sf_isabelle_test.py```. By providing the output expected, The thy file will pass only if the outputs of the execution in Isabelle are the same as which you provide.

* To get all translation files in one time, we can run:

```python3 -m unittest Semantic_Stateflow.transform_test ```

Here we give the matlab xml file and the corresponding json file in ```example_xml```, then we construct a content ```all_examples``` and all thy files in are put in this content. To check the results, you can execute the charts in Matlab and compare the outputs with the json files, then check the execution correctness in the corresponding thy files.

## Introduction to the Files

### Syntax_Final.thy and Semantics_Final.thy
* Syntax_Final.thy: the syntax for a subset of Stateflow
* Semantics_Final.thy: the big-step operational semantics of the Stateflow subset.

### Final_ML.thy
* The tactic for the automatic execution of the Stateflow semantics.

### sf_isabelle.py, sf_isabelle_test.py and transform_test.py
* sf_isabelle.py: a translation tool from Stateflow charts to Isabelle representations.
* sf_isabelle_test.py: the corresponding test code of the translation tool.
* transform_test.py: a test tool to get all translation files in one time

### info.json
* A templete json file which provides the input parameters and the outputs you want to get.

### example_xml
* All Stateflow examples in xls format and xml format

### example_thy
* All test Stateflow examples in .thy format


