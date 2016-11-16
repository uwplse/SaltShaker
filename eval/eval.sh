#! /bin/bash

cd /x86sem/eval

segments=( 'zaa' 'zab' 'zac' 'zad' 'zae' 'zaf' 'zag' 'zah'
           'zai' 'zaj' 'zak' 'zal' 'zam' 'zan' 'zao' )

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

