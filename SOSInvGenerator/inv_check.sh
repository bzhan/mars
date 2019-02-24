#!/bin/bash

#input from Isabelle
args="$*"

cd $MARSHOME/SOSInvGenerator

echo $args > input.json

python3 redlog_generator.py > input

cd $REDUCEHOME

./reduce $MARSHOME/SOSInvGenerator/input
cat output
rm output

cd $MARSHOME/SOSInvGenerator
rm input input.json
