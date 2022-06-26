// spin -p -s -r -X -v -n123 -l -a -u10000 counter.pml
// Verifying Manual: https://spinroot.com/spin/Man/Roadmap.html
// spin -a spec

// Shared counter variable.
byte c = 0

// Increments c.
proctype counter() {
    byte temp = 0;  // Temp c.
    byte i = 0;  // Index to remember count loop.

    // Executing a do statement:
    // - Non-deterministically choose a non-blocking branch (::) i.e. branch with true statement.
    // - If every branch is blocking then we're deadlocked.
    do
    :: i < 10 ->  // Branches are denoted by ::.
        temp = c;
        c = temp + 1;
        i = i + 1;
    :: i >= 10 ->
        break;
    // :: else -> ... // Is a non-blocking branch.
    od
}

init {
    run counter();
    run counter();

    _nr_pr == 1 // guard: blocks until condition becomes true.
                // _nr_pr is a special variable counting the number of running processes.

    assert (10 <= c && c <= 20);
}