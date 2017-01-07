#!/bin/sh

oldln=$1
newln=$2
file="$3"

#if [ $(( $oldln > $newln )) ]
if [ $oldln -gt $newln ]
then
  echo "Going up"
  prefix=$(( $newln - 1 ))
  head -n $prefix "$file"

  sed $oldln'!d' "$file"

  midlen=$(( $oldln - $newln ))
  tail -n +$newln "$file" | head -n $midlen

  suffix=$(( $oldln + 1 ))
  tail -n +$suffix "$file"
else
  echo "Going down"
  prefix=$(( $oldln - 1 ))
  head -n $prefix "$file"

  midlen=$(( $newln - $oldln ))
  midstart=$(( $oldln + 1 ))
  tail -n +$midstart "$file" | head -n $midlen

  sed $oldln'!d' "$file"

  suffix=$(( $newln + 1 ))
  tail -n +$suffix "$file"
fi
