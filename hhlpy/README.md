# HHLPy

HHLPy is a formal verification tool for hybrid systems. It is based on an
extension of Hoare logic to hybrid systems called Hybrid Hoare Logic. 
Performance data of HHLPy on benchmarks and case studys are given in `performance_data.txt`.

## Installation

### Prerequisites
* Install Python 3.9 or higher: https://www.python.org/downloads/.
* (Optional) Install Wolfram Engine (Detailed installation steps are given below).

### Install Using pip (Recommended)
Note that you do not need to clone the repository.
* Run `pip install hhlpy` or `python -m pip install hhlpy` to install HHLPy.
* Run `python -m hhlpy` to start HHLPy. Your browser should open automatically.
  (If it doesn't, open `http://127.0.0.1:8000/` in your browser.)
  
### Install Using git
* Install NodeJS: https://nodejs.org/en/.
* Clone the library’s repository:
```
>>> git clone git@github.com:bzhan/mars.git
```
* Install required packages:
```
>>> python -m pip install -r requirements.txt
```
* Install node modules:
```
>>> cd hhlpy/gui
>>> npm install
```
* Run `npm run serve` to start HHLPy. Open `http://127.0.0.1:8080/` in your browser.

### Install Wolfram Engine

To be able to proof more verification conditions, install Wolfram Engine on your system:
* Download Wolfram Engine and install it: https://www.wolfram.com/engine/
* Get a license for Wolfram Engine and activate it.
* If you use the standard installation path, HHLPy should be able to
find it automatically. If you use a nonstandard installation path, you
need to set the environment variable `WolframKernel` to the path of the file
`WolframKernel` or `WolframKernel.exe` that comes with the Wolfram Engine
installation.
* If you see the line `Socket exception: Socket operation aborted.` in the terminal,
you probably still need to activate your license. 

## First Steps

Click on the file `basic1.hhl` in the list of example files on the left panel. A
file with the following content will open:
```
pre [x >= 0];
x := x+1;
post [x >= 1];
```
This example program has a single instruction: it increases the variable x by 1.
The only precondition is `x >= 0`; the only postcondition is `x >= 1`.
These conditions seem correct: If `x` is at least `0` and increased by `1`, it
is at least `1` afterwards.

On the right side, you see the verification condition panel. It contains a
single verification condition that has been generated from the program:
```
assume:
  x >= 0
show: x + 1 >= 1
```
Click on the button `Verify` to check the verification condition. A green
checkmark appears below the condition. And the counter next to the button
indicates that `1/1` verification conditions have been proved.

Next, add a second instruction to the program that divides x by 2:
```
pre [x >= 0];
x := x+1;
x := x/2;
post [x >= 1];
```
Observe that the verification condition on the right updates automatically.
Click the button `Verify` to verify the new condition. You will see an X mark
indicating that the verification condition could not be verified. Try to adapt
the postcondition to make the verification go through...

Explore the other example files to see more!
