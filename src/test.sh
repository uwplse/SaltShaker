main=.build/main.rkt

$main construct-positive-space 32
echo 
$main trivial-positive-verification 10
echo 
$main find-word-proposition 32
echo 
$main find-word 32
echo 
$main word-verification 32
echo 
$main init-rtl-state
echo 
$main cast8-add-verification-proposition
echo 
$main cast8-add-verification
echo 
$main not-verification-proposition
echo 
$main not-verification

