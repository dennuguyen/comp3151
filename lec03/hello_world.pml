// Process type: process that we can spawn instances of.
proctype P() {
    // _pid: process id.
    printf("=========Hello world, my PID is %d!\n", _pid);
}

// Special process that is active at startup.
// Can have at most 255 processes at a time.
// init {
//     run P();  // Spawn an instance of P.
//     run P();  // Spawn another instance of P.
//     run P();  // ...
// }

// Each ; statement is an independent event.
// For systems with fixed number of processes.
// We should spawn processes at same time.
init {
    // Everything inside happens at the same time.
    atomic {
        run P();
        run P();
        run P();
    }
}

// Promela Manual: http://spinroot.com/spin/Man/Quick.html
// CLI Manual: https://man.archlinux.org/man/community/spin/spin.1.en

// spin -n123 -p -s -r -X -v -l -g -u10000 hello_world.pml
// -i for interactive mode.