#!/bin/sh

echo "Running '$0'"
dir=`dirname "$0"`/"benchmarks"
#subdirs=`find "$dir" -type d`

#for d in $subdirs
#do
  #ls "$d"/*.scala
  #if [ $? = 0 ]
  #then
    #pkg=`echo "$d" | sed s/\\\.\\\/repo\\\///g | sed s/src\\\/main\\\/scala\\\///g | sed s/\\\//\./g`
    #echo "import scala.scalanative.$pkg._" >> Codebase.scala
  #fi
#done

ls $dir
find "$dir" -name *.scala
