#!/bin/bash
echo  "The invariant template is:\n"
cat $MARSHOME/QEInvGenerator/template
echo  "\n\nPlease select parameters which are set to 0 like 1,3,5\n"
cat $MARSHOME/QEInvGenerator/tempPara
read paraIdx
echo $paraIdx > $MARSHOME/QEInvGenerator/filePara

