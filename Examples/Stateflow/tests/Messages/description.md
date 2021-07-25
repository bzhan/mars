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

* This example is taken from the user's guide, showing messages remain in the queue after 3 seconds. The example also demonstrates sending messages from another chart.
* Expected result (6 iterations)
  - en_A
  - en_A0
  - en_A1
  - en_A2

### Messages4

* This example demonstrates that even after a message expires, conditions on the message can still be evaluated.
* Expected result (3 iterations)
  - en_A
  - en_B
  - en_C

### Messages5

* This example shows that messages in the queue can be skipped. The first test on M1 takes out the second message, so the first message with M1.data equal to 4 is skipped.
* Expected result (4 iterations)
  - en_A
  - en_B (wait for 1 iteration)
  - en_C

### Messages6

* In this example, the first M1 message with data 4 is skipped. The remaining operations on M1 uses the second and third messages.
* Expected result (5 iterations)
  - en_A
  - en_B (wait for 1 iteration)
  - en_C
  - en_D
  - en_E

### Messages7

* This example shows that without message events, no new message is retrieved from the queue, so the final transition checking for M1.data == 2 never passes.
* Expected result (4 iterations)
  - en_A
  - en_B
  - en_C
  - en_D
