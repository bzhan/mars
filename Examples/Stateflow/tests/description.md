## Extra case studies

### settaDemo

* A simple example illustrating inner transitions, junctions, and sending of events.
* Expected result (1 iteration):
  - B
  - D
  - A
  - D

### RTPS

* Model of Real-Time Publish and Subscribe protocol.
* Expected result: all messages sent from the writer side to the reader side.

### StopWatch1

* Test of sequence START, LAP, LAP. 
* Start counting with a freeze of display in the middle.

### StopWatch2

* Test of sequence START, LAP, LAP periodically.
* Periodically start counting with a freeze of display in the middle.

### StopWatch3

* Test of sequence START, LAP, LAP, START, START.
* The second START stops counting, the third START resumes where it left off.

### StopWatch4

* Test of sequence START, START, LAP, LAP, START.
* The first LAP event will reset time to zero, so the third START resumes
  counting from zero.

### StopWatch5

* Test of sequence START, LAP, START, START, LAP.
* The second and third START stops and resumes counting, but does not reset clock.

### StopWatch6

* Test of sequence START, LAP, START, LAP, START.
* The stop watch traverses Reset, Running, Lap and LapStop states in a loop.
  Clock is not reset to zero between second and third START.
