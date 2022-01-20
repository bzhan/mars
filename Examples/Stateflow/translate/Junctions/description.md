## Examples of junctions

### Junctions1

* This example demonstrates priority order when evaluating junctions.
* Expected result:
  - enA
  - enD

### Junctions2

* This example shows the possibility that transitions from two different states can meet in the same junction. It also shows the interaction between condition actions and transition actions (all condition actions are executed before all transition actions).
* Expected result (2 iterations):
  - enA
  - exA
  - enB
  - conBJun
  - conJunC
  - exB
  - tranBJun
  - tranJunC
  - enC

### Junctions3

* This example shows a loop in junctions. Note only condition actions can appear in the loop.
* Expected result:
  - t1
  - t2
  - t1
  - t2
  - t1
  - t2
  - t1
  - t4

### Junctions4

* This example shows that the location of junctions does not really matter. Here even though the middle junction is in B, the state B is never entered.
* Expected result:
  - enA
  - enA1
  - duA
  - c1
  - c2
  - exA1
  - exA
  - t1
  - t2
  - enC
  - enC2

### Junctions5

* A more complicated example also showing that locations of junctions do not matter. Even though the search entered a junction in C, state C is never entered.
* Expected result:
  - enA
  - enA1
  - duA
  - ca
  - exA1
  - enA2

### Junctions6

* This example demonstrates some complicated backtracking. Note how f("ca") will be executed multiple times.
* Expected result:
  - enA
  - ca
  - ca
  - exA
  - ta2
  - ta4
  - enC

### Junctions7

* There can be an exponential number of possible transition paths that need to be remembered.
* Expected result:
  - enA
  - exA
  - xle2
  - yeq2
  - zge2
  - enC

### Junctions8

* Junctions can connect both inner and outer transitions from the same state.
* Expected result (3 iterations):
  - enA
  - ca1
  - exA
  - enC
  - exC
  - enA
  - duA
  - ca2
  - exA
  - enC
