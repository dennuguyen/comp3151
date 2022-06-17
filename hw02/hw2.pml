// Does Dekker's algorithm work for 3 or more processes?

bit wantA = 0
bit wantB = 0
bit wantC = 0
bit turnA = 0
bit turnB = 0
bit turnC = 0

proctype A() {
    do
    :: true ->
        wantA = 1;
        do
        :: turnB == 1 ->
            wantA = 0;
            waitA: 
        :: turnC == 1 ->
        od
    od
}

proctype B() {

}

proctype C() {

}

init {
    run A();
    run B();
    run C();
}
