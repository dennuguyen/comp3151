promela_stem=$(basename "$1" .pml)

spin -a $1

gcc -O2 -o pan pan.c

./pan "${@:2}"

rm pan pan.b pan.c pan.h pan.m pan.p pan.t