## Examples of states (entry, during and exit actions)

### States1

* A basic example demonstrating the order of entry into states, and the order of executing during actions.
* Expected result (3 iterations)
  - enA
  - enA1
  - duA
  - exA1
  - enA2
  - duA
  - duA2
  - duA
  - duA2

### States2

* Example showing order of exiting and entry into states during an outer transition.
* Expected result (3 iterations)
  - enA
  - enA1
  - exA1
  - exA
  - enB
  - enB1
  - duB
  - duB1
  - duB
  - duB1

### States3

* Example demonstrating entry, during and exit actions for AND states.
* Expected result (2 iterations)
  - enA
  - enA1
  - enA2
  - exA2
  - exA1
  - exA
  - enB
  - enB1
  - enB2
  - duB
  - duB1
  - duB2

### States4

* This example demonstrates transitions on the upper level of the hierarchy has priority over transitions on the lower level. The transitions to A2 and B2 are never carried out.
* Expected result (3 iterations)
  - enA
  - enA1
  - enB
  - enB1
  - enA
  - enA1
  - enB
  - enB1
