#!/bin/bash

#input from Isabelle
args="$*"

cd $MARSHOME/SOSInvGenerator

echo $args > input.json

python3 script_generator.py > sos_input.m

$MATLABHOME/matlab -nodesktop -nosplash -r sos_input
