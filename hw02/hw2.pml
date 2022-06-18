// Does Dekker's algorithm work for 3 or more processes?
// Yes, but hard to maintain and scale.

#define MutexDontCare
#include "critical2.h"

bit wantA = 0
bit wantB = 0
bit wantC = 0
byte turn = 0   // 0 = A, 1 = B, 2 = C

proctype A() {
    do
    :: non_critical_section();
        waitA: wantA = true
        do
        :: wantB || wantC ->
            if
            :: turn != 1 ->
                wantA = false;
                turn == 1;
                wantA = true;
            :: else -> skip
            fi
        :: else -> break
        od
        csA: critical_section();
        turn = 1;
        wantA = false;
    od
}

proctype B() {
    do
    :: non_critical_section();
        waitB: wantB = true
        do
        :: wantA || wantC ->
            if
            :: turn != 2 ->
                wantB = false;
                turn == 2;
                wantB = true;
            :: else -> skip
            fi
        :: else -> break
        od
        csB: critical_section();
        turn = 2;
        wantB = false;
    od
}

proctype C() {
    do
    :: non_critical_section();
        waitC: wantC = true
        do
        :: wantA || wantB ->
            if
            :: turn != 3 ->
                wantC = false;
                turn == 3;
                wantC = true;
            :: else -> skip
            fi
        :: else -> break
        od
        csC: critical_section();
        turn = 3;
        wantC = false;
    od
}

init {
    run A();
    run B();
    run C();
}

/**
spin -search -ltl mutex hw2.pml

By default, safety properties are checked.

No failed assertions raised.
 */
ltl mutex { [] !(A@csA && B@csB && C@csC) }

/**
spin -search -a -ltl waitA hw2.pml

-a flag enables checking for acceptance cycles (liveness).

No failed assertions raised.
 */
ltl waitA { [] (A@waitA implies (<> A@csA)) }

/**
spin -search -a -ltl waitB hw2.pml

-a flag enables checking for acceptance cycles (liveness).

No failed assertions raised.
 */
ltl waitB { [] (B@waitB implies (<> B@csB)) }

/**
spin -search -a -ltl waitC hw2.pml

-a flag enables checking for acceptance cycles (liveness).

No failed assertions raised.
 */
ltl waitC { [] (C@waitC implies (<> C@csC)) }