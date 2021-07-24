## Examples of transitions (inter-level and inner transitions)

### Transitions1

* A simple example of an inter-level transition (also called super-transition). Note also the difference between condition action and transition action.
* Expected result:
  - enS
  - enA
  - ca
  - exA
  - exS
  - ta
  - enT
  - enB

### Transitions2

* A slightly more complicated example, this time with the target one level above in the hierarchy.
* Expected result (2 iterations):
  - enS
  - enA
  - exA
  - enB
  - ca
  - exB
  - exS
  - ta
  - enT
  - enB

### Transitions3

* Interaction between inter-level transitions and history junctions. After reaching c2 for the first time, each time A is entered again we go directly to c2.
* Expected result (5 iterations):
  - b
  - c1
  - c2
  - B
  - c2
  - B

### Transitions4

* An example of an inner transition. The transition can be considered as from S to its child state A. This requires exiting from substates of S (that is, exA), then enter A.
* Expected result:
  - enS
  - condDefault
  - tranDefault
  - enA
  - duS
  - condInner
  - exA
  - tranInner
  - enA

### Transitions5

* An example of an inner state from a state to the same state. Note S is not exited or entered, but the child state of S is.
* Expected result:
  - enS
  - enA
  - duS
  - condInner
  - exA
  - tranInner
  - enA

### Transitions6

* An example of an inner transition to a child state A to its parent S. Again, S is neither entered nor exited during the transition.
* Expected result (2 iterations):
  - enS
  - enA
  - duS
  - exA
  - enB
  - duS
  - innerCond
  - exB
  - innerTran
  - enA

### Transitions7

* This example demonstrates the ordering between outer and inner transitions. If one of the outer transitions can be carried out, then no inner transitions are tried.
* Expected result:
  - enS
  - enT

### Transitions8

* This example demonstrates ordering between the inner transitions.
* Expected result:
  - enS
  - duS
  - ca1
  - duS
  - ca1
  - duS
  - ca2
  - duS
  - ca2
  - enT
