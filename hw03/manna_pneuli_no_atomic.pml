#define MutexDontCare
#include "critical2.h"

int wantp = 0
int wantq = 0

proctype P() {
    do
    :: true ->
p1:     non_critical_section();
p2:     if
        :: wantq == -1 ->
            wantp = -1
        :: else ->
            wantp = 1
        fi 
        do
        :: wantq == wantp ->
p3:        skip
        :: else -> break
        od
p4:     critical_section();
p5:     wantp = 0;
    od
}

proctype Q() {
    do
    :: true ->
q1:     non_critical_section();
q2:     if
        :: wantp == -1 ->
            wantq = 1
        :: else ->
            wantq = -1
        fi 
        do
        :: wantq == -wantp ->
q3:        skip
        :: else -> break
        od
q4:     critical_section();
q5:     wantq = 0;
    od
}

init {
    run P();
    run Q();
}

ltl mutex { [] !(P@p4 && Q@q4) }