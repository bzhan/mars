## Examples for data store memory

### Communication1

* Basic example of communication. Chart2 receives two values a and b from Chart1, which becomes a_in and b_in in Chart2.
* Expected result (6 iterations):
  - en_A
  - en_A1
  - en_B
  - 2 1
  - en_A
  - 2 2
  - en_B
  - 3 2
  - en_A
  - 3 3
  - en_B
  - 4 3
  - en_A
  - 4 4

### Communication2

* This example shows inputs from Simulink blocks.
* Expected result (6 iterations):
  - en_A
  - en_A1
  - en_B
  - 1 2 2 1
  - en_A
  - 1 2 2 2
  - en_B
  - 1 2 3 2
  - en_A
  - 1 2 3 3
  - en_B
  - 1 2 4 3
  - en_A
  - 1 2 4 4

### Communication3

* This example shows that with communication, the sending chart always runs first (regardless of the alphabetical ordering of names).
* Expected result (6 iterations):
  - en_A
  - en_A1
  - en_B
  - 2 1
  - en_A
  - 2 2
  - en_B
  - 3 2
  - en_A
  - 3 3
  - en_B
  - 4 3
  - en_A
  - 4 4

### Communication4

* This example shows chaining of input/outputs.
* Expected result (6 iterations):
  - en_A
  - en_A1
  - en_B
  - 2 2
  - en_A
  - 2 4
  - en_B
  - 3 4
  - en_A
  - 3 6
  - en_B
  - 4 6
  - en_A
  - 4 8

### Communication5

* This example shows combination of input/output with data store memory. The order of execution follows send-then-receive order, not alphabetical order.
* Expected result (6 iterations):
  - en_A
  - en_C
  - en_A1
  - en_B
  - 2 2 2
  - en_A
  - 2 4 4
  - en_B
  - 3 4 10
  - en_A
  - 3 6 20
  - en_B
  - 4 6 42
  - en_A
  - 4 8 84

### Communication6

* Another example showing combination of input/output with data store memory. In this case, Chart2 is isolated from Chart1 and Chart3. The order of execution is Chart1 -> Chart3 -> Chart2.
* Expected result (6 iterations):
  - en_A
  - en_A1
  - en_C
  - en_B
  - 2 1
  - 1
  - en_A
  - 2 2
  - 1
  - en_B
  - 3 2
  - 2
  - en_A
  - 3 3
  - 2
  - en_B
  - 4 3
  - 3
  - en_A
  - 4 4
  - 3

### DSM1

* Single data store and single chart. Default transition sets value of data store.
* Expected result:
  - 2
  - 4
  - 5
  - 7
  - 8
  - 10

### DSM2

* Single data store and single chart. Default transition reads from data store.
* Expected result:
  - 1
  - 3
  - 4
  - 6
  - 7
  - 9

### DSM3

* Single data store and single chart. Value of data store is an array.
* Expected result:
  - 3 2
  - 3 5
  - 8 5
  - 8 13
  - 21 13
  - 21 34

### DSM4

* Single data store and two charts. Chart that comes first in alphabetical order executes first.
* Expected result:
  - A1
  - C1
  - B2
  - D4
  - A4
  - C4
  - B5
  - D7

### DSM5

* Two data store and single chart.
* Expected result:
  - 4 2
  - 4 4
  - 5 4
  - 5 6
  - 6 6
  - 6 8

### DSM6

* Single data store and two charts. Value of data store is an array.
* Mix with other features.
* Expected result:
  - en_A 0 0
  - en_A1 3 0
  - en_B 4 4
  - du_A1 4 0
  - en_A 4 -1
  - du_A1 3 -1
  - en_B 4 -1
  - du_A1 4 0
