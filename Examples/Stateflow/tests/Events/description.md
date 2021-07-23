## Examples of events and directed events

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
