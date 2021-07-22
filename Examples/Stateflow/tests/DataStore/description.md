## Examples for data store memory

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
