#!/bin/sh

for d in `ls -1`
do
  nirfiles=`find $d -name *.hnir`
  if [ ! -z "$nirfiles" ]
  then
    echo "$d :"
    filecount=`echo $nirfiles | wc -w`
    linecount=`cat $nirfiles | wc -l`
    echo "  $filecount files"
    echo "  $linecount lines"
  fi
done
