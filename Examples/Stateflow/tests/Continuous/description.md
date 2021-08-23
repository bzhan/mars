## Examples of continuous evolution

### Continuous1

* A simple example of differential equation with constant derivatives.
* Expected result:
  - enA 0.000 0.000  (delay 0.5)
  - conAB1 1.000 0.500
  - exA 1.000 0.500
  - tranAB1 1.000 0.500
  - enB 1.000 0.500
  - enB1 0.000 0.500

### Continuous2

* Differential equation for a circle. Note with variable-step solver, can find the exact crossing point.
* Expected result:
  - enA 0.000 1.000  (delay pi/6~=0.524)
  - conAB1 0.500 0.866
  - exA 0.500 0.866
  - tranAB1 0.500 0.866
  - enB 0.500 0.866
  - enB1 0.000 0.866

### Continuous3

* This example demonstrates the common occurring position-velocity-acceleration system.
* Expected result:
  - enA 0.000 0.000  (delay sqrt(2)~=1.414)
  - conAB1 1.414 1.000
  - exA 1.414 1.000
  - tranAB1 1.414 1.000
  - enB 1.414 1.000
  - enB1 0.000 1.000

### Continuous4

* An example with two outer transitions.
* Expected result:
  - enA 0.000 0.000  (delay 1)
  - conAB 1.000 0.500
  - exA 1.000 0.500
  - tranAB 1.000 0.500
  - enB 1.000 0.500
  - enB1 0.000 0.500

### Continuous5

* An example with hierarchical states.
* Expected result:
  - enA
  - enA1
  - enA2
  - exA
  - enB

### Continuous6

* An example with competing transition out of A and out of A2.
* Expected result:
  - enA
  - enA1
  - enA2
  - condA2B
  - exA
  - enB
