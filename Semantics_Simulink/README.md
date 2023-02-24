  
# Code for Semantics of Simulink in Isabelle:

## Introduction to the Files

### Permutation.thy
* The definition and related lemmas of permutation.

### DiscreteSyntax.thy
* Syntax of discrete blocks, block sorting, calculation of inherited sample time.

### DiscreteSemantics.thy
* Semantics of discrete blocks, existence and uniqueness of discrete blocks.

### ContinuousSyntax.thy
* Syntax of continuous blocks, the combination of integrator blocks into one single integrator block.

### DisConSemantics.thy
* Semantics of continuous blocks, existence and uniqueness of continuous blocks; Semantics of disctere-continuous blocks, existence and uniqueness of discrete-continuous blocks

### example.slx and example.thy
* example.slx: A Simulink example with discrete and continuous blocks.
* example.thy: Execution of the example in Isabelle.


