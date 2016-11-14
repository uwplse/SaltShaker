#! /bin/bash

cd /x86sem/eval

segments=( 'xab' 'xac' 'xad' 'xae' 'xaf' 'xag' 'xah'
           'xai' 'xaj' 'xak' 'xal' 'xam' 'xan' 'xao' )

cat xaa > next
../src/racket/compareAll.rkt next
cat xaa > explored

for i in "${segments[@]}"
do
    cat $i >> next
    ../src/racket/compareAllInc.rkt next explored
    cat $i >> explored
done

rm next
rm explored
