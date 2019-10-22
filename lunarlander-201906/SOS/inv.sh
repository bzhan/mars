#!/bin/bash

#input from Isabelle
args="$*"

cd $MARSHOME/SOSInvGenerator

echo $args > input

#read user-specified invariant degree T
gnome-terminal -e "bash setDegree.sh"
while test ! -e degree
do
   sleep 1
done

#execute the Mathematica script to generate Matlab script
$MATHEMATICAHOME/math -script ScriptGenerator >garbage

#generate sos-based invariant
$MATLABHOME/matlab -nodesktop -nosplash -r sosInv > output

#check the generated invariant
$MATHEMATICAHOME/math -script InvChecker

#remove intermediate files
#if test -e *~
#then rm *~
#fi

rm input garbage sosInv.m degree
