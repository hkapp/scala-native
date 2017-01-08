#!/bin/sh

repo="/media/Data/Documents/EPFL/ScalaNative/repo"
driver="$repo/tools/src/main/scala/scala/scalanative/optimizer/Driver.scala"
#output="$repo/benchmarks/"

find_bounds() {
  startln=`sed -n '/pass\./=' "$driver" | head -n 1`
  endln=`sed -n '/pass\.MainInjection/=' "$driver" | head -n 1`
  endln=$(( $endln - 1 ))
  range=$(( ( $endln - $startln ) + 1 ))
}

measure() {
  sbt benchmarks/nativeLink > /dev/null

  if [ -z $output ]
  then
    output=`ls -1 $repo/benchmarks/target/scala-2.11/*.hnir | tail -n 1`
  fi

  loc=`cat $output | wc -l`
}

rand() {
  #r=$(( ( $RANDOM % $range ) + $startln ))
  shuf -i $startln-$endln -n 1
}

flip() {
  a=`rand`
  b=`rand`
  while [ $a -eq $b ]
  do
    b=`rand`
  done

  name=`sed $a'!d' "$driver" | sed s/'\ '//g | sed s/','//g`
  echo "Trying $name in position $(( $b - $startln + 1 ))"
  sh "$repo/codebase/insert.sh" $a $b "$driver" > "$driver".tmp
  mv "$driver".tmp "$driver"
}

cd $repo

find_bounds
echo "Start at $startln, end at $endln"

measure
echo "Starting with $loc lines"
best=$loc

cp "$driver" "$driver".bak

while [ 1 ]
do
  flip
  measure
  if [ $loc -lt $best ]
  then
    best=$loc
    cp "$driver" "$driver".bak
    echo "Found a better placement with $loc lines"
  else
    echo "Bad placement, with $loc lines"
    cp "$driver".bak "$driver"
  fi
done
