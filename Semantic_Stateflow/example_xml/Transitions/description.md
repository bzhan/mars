## Examples of transitions (inter-level and inner transitions)

### Transitions1

* A simple example of an inter-level transition (also called super-transition). Note also the difference between condition action and transition action.
* Expected result:
  - enS
  - enA
  - ca
  - exA
  - exS
  - ta
  - enT
  - enB

### Transitions2

* A slightly more complicated example, this time with the target one level above in the hierarchy.
* Expected result (2 iterations):
  - enS
  - enA
  - exA
  - enB
  - ca
  - exB
  - exS
  - ta
  - enT
  - enB

### Transitions3

* Interaction between inter-level transitions and history junctions. After reaching c2 for the first time, each time A is entered again we go directly to c2.
* Expected result (5 iterations):
  - b
  - c1
  - c2
  - B
  - c2
  - B

### Transitions4

* An example of an inner transition. The transition can be considered as from S to its child state A. This requires exiting from substates of S (that is, exA), then enter A.
* Expected result:
  - enS
  - condDefault
  - tranDefault
  - enA
  - duS
  - condInner
  - exA
  - tranInner
  - enA

### Transitions5

* An example of an inner state from a state to the same state. Note S is not exited or entered, but the child state of S is.
* Expected result:
  - enS
  - enA
  - duS
  - condInner
  - exA
  - tranInner
  - enA

### Transitions6

* An example of an inner transition to a child state A to its parent S. Again, S is neither entered nor exited during the transition.
* Expected result (2 iterations):
  - enS
  - enA
  - duS
  - exA
  - enB
  - duS
  - innerCond
  - exB
  - innerTran
  - enA

### Transitions7

* This example demonstrates the ordering between outer and inner transitions. If one of the outer transitions can be carried out, then no inner transitions are tried.
* Expected result:
  - enS
  - enT

### Transitions8

* This example demonstrates ordering between the inner transitions.
* Expected result:
  - enS
  - duS
  - ca1
  - duS
  - ca1
  - duS
  - ca2
  - duS
  - ca2
  - enT
  
### TransitiontoMultipleDestinations

* This example demonstrates transition to multiple destinations with event E_two.
* Expected result:
  - Entry A
  - Exit A
  - Entry C
  
### TransitionSegment

* This example demonstrates transition to multiple destinations with event E_one.
* Expected result:
  - Entry A
  - Condition Action2
  - Exit A
  - Transition Action1
  - Entry C
  
### TransitionCommonEvent

* This example demonstrates the order of transitions with event E_one.
* Expected result:
  - Entry A
  - Exit A
  - Entry B
  - Exit B
  - Entry C
  
### Trans_State2State

* This example aim to tell readers to avoid cycles in transition send.
* Expected result:
  - Entry_On
  - Exit_On
  - Entry_Off

### Substate2Substate

* Interaction between inter-level transitions
* Expected result:
  - EntryA
  - EntryA1
  - DuringA
  - ExitA1
  - ExitA
  - transition_action
  - EntryB
  - EntryB1
  
### MultipleSourcesTransition

* Multiple sources transition
* Expected result:
  - Entry A
  - Exit A
  - Entry C
  
### LabeledDefaultTransition

* an example with multiple default transitions in a state, controlled by different event
* Expected result:
  - Entry A
  - Exit A
  - Entry B
  - Entry B1(with E_one) or Entry B2(with E_two)

### InnerTransitiontoJunction

* An example of an inner transition to a junction
* Expected result:
  - Entry A
  - Entry A1
  - During A
  - Exit A1
  - Entry A2
  
### InnerTransitiontoHistoryJunction

* An example of an inner transition to a history junction
* Expected result:
  - Entry A
  - Entry A1
  - During A
  - Exit A1
  - Entry A1
  
### InnerTransition1

* An example of an inner transition
* open .thy for the result

### If_Then_Else

* An example of a junction to stand for if-then-else
* Expected result:
  - Entry A
  - Condition Action3
  - Exit A
  - Transition Action1
  - Entry B

### DefaultTransitiontoState

* A simple example of default transition
* Expected result:
  - Entry A
  - Exit A
  - Transition Action
  - Entry B
  - Entry B1
  
### DefaultTransitiontojunction

* A simple example of default transition to a junction
* Expected result:
  - Entry A
  - Exit A
  - Transition Action
  - Entry B
  - Entry B1
  
### DefaultTransitiontojunction2

* A complex example of default transition to a junction
* Expected result:
  - Entry A
  - Exit A
  - Entry B
  - Entry B2
  - Entry B2a
  - Entry B1
  - Entry B1a
  
### ConditionTransitionAction

* A simple example of condition action and transition action.
* Expected result:
  - Entry A
  - Condition Action
  - Exit A
  - Transition Action
  - Entry B

### ConditionActionLoop

* An example of transition loop
* Expected result:
  - Entry A
  - 1 2 3 4 5 6 7 8 9 10
  - Exit A
  - Entry B
  
### ConditionAction
* A simple example of branch
* Expected result:
  - Entry A
  - Condition Action
  - Exit A
  - Entry B
