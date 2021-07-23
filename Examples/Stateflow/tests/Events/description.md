## Examples of events and directed events

### Event1

* Simple example of events. Event raised in B can be catched by A (the entire diagram is executed again).
* Expected result:
  - b
  - a
  - en_A2
  - tb
  - en_B2

### Event2

* This example demonstrates that a single event can cause multiple transitions from different charts.
* Expected result:
  - b
  - a
  - en_A2
  - c
  - en_C2
  - tb
  - en_B2

### Event3

* This example demonstrates that a single event can cause multiple transitions in junctions.
* Expected result:
  - b
  - a1
  - a2
  - en_A2
  - tb
  - en_B2

### Event4

* This example shows a nested event. When event E is handled in A, event F is raised. After event F returns, event E still remains so the second transition after the junction can be carried out.
* Expected result:
  - b
  - a1
  - c
  - en_C2
  - a2
  - en_A2
  - tb
  - en_B2

### Event5

* This example shows that transitions without event marking will accept any event. Chart A will perform two transitions in one iteration, the first on its own and the second in response to event E.
* Expected result:
  - en_A2
  - b
  - en_A3
  - tb
  - en_B2

### Event6

* This example tests handling of deep recursions.
* Expected result:
  - a 5
  - a 4
  - a 3
  - a 2
  - a 1
  - a 0
  - en_A2 0

### DirectedEvent1

* Standard example of directed events. Each of A, B and C take events E_one and E_two, so directed events are used to distinguish between them.
* Expected result:
  - en_A1
  - en_B1
  - en_C1
  - ex_C1
  - en_C2
  - ex_B1
  - en_B2
  - ex_A1
  - en_A2
  - ex_A2
  - en_A1
  - ex_B2
  - en_B1
  - ex_C2
  - en_C1

### DirectedEvent2

* Similar to DirectedEvent1, but with repeated names of states within A, B, and C.
* Expected result:
  - en_A1
  - en_B1_A1
  - en_C1_A1
  - ex_C1_A1
  - en_C2_A2
  - ex_B1_A1
  - en_B2_A2
  - ex_A1
  - en_A2
  - ex_A2
  - en_A1
  - ex_B2_A2
  - en_B1_A1
  - ex_C2_A2
  - en_C1_A1

### DirectedEvent3

* Similar to the previous two examples, but using the send keyword.
* Expected result:
  - en_A1
  - en_B1
  - ex_B1
  - en_B2
  - ex_A1
  - en_A2

### DirectedEvent4

* A complex example combining several elements.
* Expected result:
  - en_A1
  - en_B2
  - en_B21
  - ex_B21
  - ex_B2
  - en_B4
  - ex_A1
  - en_A2

### DirectedEvent5

* A variant of DirectedEvent4, with more specific target.
* Expected result:
  - en_A1
  - en_B2
  - en_B21
  - ex_B21
  - en_B22
  - ex_A1
  - en_A2

### DirectedEvent6

* A combination of directed event with early return.
* Expected result:
  - a
  - c
