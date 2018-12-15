#!/bin/bash

args="$*"

#Read order of invariant template
if test -e $MARSHOME/QEInvGenerator/fileN
then
rm $MARSHOME/QEInvGenerator/fileN
fi
gnome-terminal -x bash -c "bash $MARSHOME/QEInvGenerator/inputN.sh"
while test ! -e $MARSHOME/QEInvGenerator/fileN
do
	sleep 1
done


#Process the input and generate the template
echo "$MARSHOME/QEInvGenerator/QEInputProcess \"$args\"" > $MARSHOME/QEInvGenerator/cmdFile
processedInput=`source $MARSHOME/QEInvGenerator/cmdFile`



#Choose parameters of invariant template
if test -e $MARSHOME/QEInvGenerator/filePara
then
rm $MARSHOME/QEInvGenerator/filePara
fi
gnome-terminal -x bash -c "sh $MARSHOME/QEInvGenerator/choosePara.sh"
while test ! -e $MARSHOME/QEInvGenerator/filePara
do
	sleep 1
done


#Get result
mathInput="input:=$processedInput; ParaIndex:=$paraIdx"
echo "$MARSHOME/QEInvGenerator/QEInvGen \"$processedInput\"" > $MARSHOME/QEInvGenerator/cmdFile
source $MARSHOME/QEInvGenerator/cmdFile
