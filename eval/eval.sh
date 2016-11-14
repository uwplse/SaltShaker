#! /bin/bash

cd /x86sem/eval

segments=( 'xaa' 'xab' 'xac' 'xad' 'xae' 'xaf' 'xag' 'xah'
           'xai' 'xaj' 'xak' 'xal' 'xam' 'xan' 'xao' )

# segments=( 'yaa' 'yab' 'yac' 'yad' 'yae' 'yaf' 'yag' 'yah'
#            'yai' 'yaj' 'yak' 'yal' 'yam' 'yan' 'yao' )

echo "================[individual]=============================="

for i in "${segments[@]}"
do
    ../src/racket/compareAllInc.rkt $i /dev/null
done

echo "================[incremental]=============================="

rm -rf next explored
touch explored

for i in "${segments[@]}"
do
    cat $i >> next
    ../src/racket/compareAllInc.rkt next explored
    cat $i >> explored
done

rm -rf next explored

echo "================[everything]=============================="

rm -rf next
touch next

for i in "${segments[@]}"
do
    cat $i >> next
    ../src/racket/compareAllInc.rkt next /dev/null
done

rm -rf next

