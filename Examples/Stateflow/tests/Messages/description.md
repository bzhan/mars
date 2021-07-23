## Examples of messages

### Messages1

* This example demonstrates that messages expire at the end of iteration, so the second transition from B to C cannot be carried out.
* Expected result (3 iterations)
  - en_A
  - en_B

### Messages2

* This example demonstrates that messages are queued. Since the en action of A sends three messages, all actions will be eventually carried out.
* Expected result (3 iterations)
  - en_A
  - en_B
  - en_C
  - en_D

### Messages3

* This example is taken from the user's guide, showing messages remain in the queue after 3 seconds.
* Expected result (6 iterations)
  - en_A
  - en_A0
  - en_A1
  - en_A2
