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

### States5

* A simple example of history junctions.
* Expected result (10 iterations)
  - enA1
  - enA2
  - enB1
  - enB2
  - enA2
  - enA1
  - enB1
  - enB2
  - enA1
  - enA2
  - enB1

### States6

* An example of hierarchical AND states.
* Expected result
  - enA
  - enA1
  - enA2
  - enB
  - enB1
  - enB2

### States7

* An example showing entry and exit behavior for self-loops.
* Expected result (2 iterations)
  - enA
  - enA1
  - exA1
  - exA
  - enA
  - enA1
  - exA1
  - exA
  - enA
  - enA1

### States8

* A practical example of the use of a self loop, for copying arrays.
* Expected result (6 iterations)
  - loop
  - loop
  - loop
  - loop
  - loop
  - 100,200,300,400,500
  
### SelfLoop

* A practical example of the use of a self loop, with a junction.
* Expected result (5 iterations)
  - Entry A
  - Exit A
  - Entry A
  - Exit A
  - Entry A
  - Exit A
  - Entry A
  - Exit A
  - Entry A
  - Exit A
  - Transition Action1
  - Entry B
  
### HistoryJunction1

* A simple example of history junctions.
* Expected result (6 iterations)
  - Entry A
  - Exit A
  - Entry B
  - Entry B1
  - Entry B2
  - Entry B4
  - Exit B
  - Entry A
  - Exit A
  - Entry B
  - Entry B4
  
### EventAction

* An example with input event.
* Expected result
  - Entry A
  - Entry A1
  - Exit A1
  - Entry A2
