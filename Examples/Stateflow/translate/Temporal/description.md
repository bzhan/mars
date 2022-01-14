## Examples for temporal events

### Temporal1

* An example of after(x,tick). After entering each state, the system will remain in that state for three iterations (executing during action for two of these iterations).
* Expected result (10 iterations):
  - en_A
  - du_A
  - du_A
  - en_B
  - du_B
  - du_B
  - en_A
  - du_A
  - du_A
  - en_B
  - du_B

### Temporal2

* This gives an example of waiting for a random number of seconds. Note it is important to create the random number and store it in a variable first.
* Expected result: after entering into each state, the number of delays should be one less than the random number picked.

### Temporal3

* With the after(x,tick) event, the condition still holds when the number of ticks exceed x.
* Expected result (10 iterations):
  - en_A
  - du_A
  - du_A
  - du_A
  - du_A
  - en_B
  - du_B
  - du_B
  - en_A
  - du_A
  - du_A

### Temporal4

* Test of before(x,tick) event.
* Expected result (10 iterations):
  - en_A
  - du_A
  - du_A
  - en_B
  - du_B
  - du_B
  - du_B
  - du_B
  - du_B
  - du_B
  - du_B

### Temporal5

* This example tests at(x,tick) event, as well as the behavior of before without any additional constraints (carry out the transition on the first opportunity).
* Expected result (10 iterations):
  - en_A
  - du_A
  - du_A
  - du_A
  - en_B
  - en_A
  - du_A
  - du_A
  - du_A
  - en_B
  - en_A

### Temporal6

* This example shows an outer transition will reset the counter. This makes it different from during actions of states.
* Expected result (5 iterations):
  - en_A
  - en_A
  - en_A
  - en_A
  - en_A
  - en_A

### Temporal7

* Initially, the number of ticks is 1, so the transition with after(1,tick) will be able to carry out.
* Expected result (5 iterations):
  - en_A
  - en_B
  - en_A
  - en_B
  - en_A
  - en_B

### Temporal8

* Inner transitions will not reset the counter, making it the same as during actions (compare Temporal3).
* Expected result (10 iterations):
  - en_A
  - du_A
  - du_A
  - du_A
  - du_A
  - en_B
  - du_B
  - du_B
  - en_A
  - du_A
  - du_A
