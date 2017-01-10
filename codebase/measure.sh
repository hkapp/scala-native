#!/bin/sh

cmd="$1"

if [ -z $2 ]
then
  nruns=10
else
  nruns=$2
fi

counter=0

while [ $counter -lt $nruns ]
do
  start=`date +%s`
  $cmd > /dev/null
  end=`date +%s`
  echo `expr $end - $start`
  counter=`expr $counter + 1`
done
