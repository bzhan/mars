#!/bin/bash

#input from Isabelle
args="$*"

cd $MARSHOME/SOSInvGenerator

echo $args > input.json

python3 redlog_generator.py > input

./reduce input
cat output

rm input input.json output
