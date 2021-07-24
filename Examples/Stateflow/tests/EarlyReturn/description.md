## Examples of early return

### EarlyReturn1

* Standard example of early return. Broadcast of event E causes exit of A, so the remaining f("E") in the condition action is not executed.
* Expected result:
  - en_A
  - en_A1
  - ex_A1
  - ex_A
  - en_B

### EarlyReturn2

* Similar to EarlyReturn1, showing that actions prior to the broadcast event in the condition action are executed, but the transition action is not executed.
* Expected result:
  - en_A
  - en_A1
  - E
  - ex_A1
  - ex_A
  - en_B

### EarlyReturn3

* Another configuration of early return (shown in the user's manual).
* Expected result:
  - en_A 1
  - ex_A 2
  - en_C 2

### EarlyReturn4

* In this example, raising event E is moved to the transition action. However, since when E is executed, A1 has already exited, so the transition from A1 to A3 will not be carried out, and there is no early return.
* Expected result:
  - ca
  - ta
  - en_A2

### EarlyReturn5

* Another example where event E is moved to the transition action. This time, since A is still active, the transition from A to B is carried out, and since A has exited, the remaining transition action f("ta") will not be executed.
* Expected result:
  - en_A
  - en_A1
  - ex_A1
  - ex_A
  - en_B

### EarlyReturn6

* This is a variant of EarlyReturn5, where there is a loop from A to A. This will cause A1 to be entered again, and the remainder of the transition action will not be executed.
* Expected result:
  - en_A
  - en_A1
  - ex_A1
  - loop
  - ex_A
  - en_A
  - en_A1

### EarlyReturn7

* This is a variant of EarlyReturn6, where the source of the transition is different from the default state.
* Expected result (two iterations):
  - en_A
  - en_A1
  - ex_A1
  - en_A2
  - ex_A2
  - loop
  - ex_A
  - en_A
  - en_A1

### EarlyReturn8

* Combination of multiple existing elements.
* Expected result:
  - a
  - c
  - du_A1
  - b
  - a
  - c
  - ex_A1
  - en_A2
  - en_C2
  - tb
  - en_B2
  - en_C3

### EarlyReturn9

* Early return for junctions: broadcast event on the second transition.
* Expected result:
  - en_A
  - en_A1
  - pre
  - ex_A1
  - ex_A
  - en_B

### EarlyReturn10

* Early return for junctions: broadcast event on the first transition.
* Expected result:
  - en_A
  - en_A1
  - pre
  - ex_A1
  - ex_A
  - en_B

### EarlyReturn11

* This is a variant of EarlyReturn7, where A2 and A3 are changed to nested states.
* Expected result:
  - en_A
  - en_A1
  - ex_A1
  - en_A2
  - en_A2a
  - ex_A2a
  - ex_A2
  - loop
  - ex_A
  - en_A
  - en_A1

### EarlyReturn12

* This example tests early return from en action, as well as the order between execution of en action and setting of state activity variable. When A is entered, the state activity variable is set first, then the entry action raises event E. Since A is now already active, this induces transition to B, and causes early return from the entry action, so the remaining output of enA_done is not executed. This all happens during the initialization phase. The first iteration will then cause a transition to C.
* Expected result:
  - enB
  - enC

### EarlyReturn13

* This example tests early return from ex action, as well as the order between execution of ex action and setting of state activity variable. When A1 is exited, the ex action is executed before setting of state activity variable. This means the event E raised in the ex action will cause a transition from A1 to A3, inducing a recursive execution of the ex action. This happens until x is reduced to zero.
* Expected result:
  - F
  - exA1
  - exA1
  - exA1
  - exA1
  - exA1
  - exA1_done
  - enA3

### EarlyReturn14

* This is a tricky variant of EarlyReturn6, where the transition action is replaced by condition action. After handling broadcast of event E, the system leaves and reenters state A1, so the remainder of the condition action (and the transition action) will be executed. This shows that the early return logic does not care about whether the source is continually present, but only whether it is present when the event handler returns.
* Expected result:
  - en_A
  - en_A1
  - loop
  - ex_A1
  - ex_A
  - en_A
  - en_A1
  - ca
  - ex_A1
  - ta
  - en_A2
