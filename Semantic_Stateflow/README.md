  
# Code for Semantics of Stateflow in Isabelle:

We define a formal operational semantics for a subset of Stateflow and formalize it in Isabelle/HOL, and we implement an automatic translator from Stateflow to Isabelle and an execution engine based on the semantics, which generates the execution results of this model according to the semantics automatically.

* To run a test, we entry into the root and add an example path in ```Semantic_Stateflow/sf_isabelle_test.py``` and run:

```python -m unittest Semantic_Stateflow.sf_isabelle_test```

then check the result is Semactic_Stateflow/example_name.thy

* Translator code is ```sf_isabelle.py```

* Semantics and engine code files are ```Semactic_Final.thy``` and ```Final_ML.thy```

* All Stateflow examples at ```example_xml``` and ```example_thy``` is for all examples in .thy format.


