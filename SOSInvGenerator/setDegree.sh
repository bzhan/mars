#!/bin/bash

function isint (){
    if [ $# -lt 1 ]; then
        return 0
    fi
 
    if [[ $1 =~ ^-?[1-9][0-9]*$ ]]; then
        return 1
    fi
 
    if [[ $1 =~ ^0$ ]]; then
        return 1
    fi
 
    return 0
}

again(){
   read -p "Please specify the highest degree of the invariant: " T

   isint $T
   if [ $? = 1 ]; then
      echo $T > degree
      exit
   else 
      echo "Invalid integer as degree."
      again
   fi
}

again
