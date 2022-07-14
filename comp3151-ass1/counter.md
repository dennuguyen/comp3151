# ASS1 - Dan Nguyen (z5206032)

## Summary

## Requirements

Let:
- `B` denote the number of bytes in `c`.
- `R` denote the number of reader processes.
- `k` denote the number of rounds of (writing, reading) each process should perform.

Like every good engineer, we need to identify the requirements of our solution:
- The inputs of the program are `R`, `B`, and `k`.
- `B > 1`.
- `R > 0`.
- `k = 0` denotes an infinite number of rounds.
- There must be a finite counter `c` with range $[0..2^{8B - 1}]$.
- There must be exactly 1 `writer` process.
- The `writer` process increments `c`.
- The `reader` process reads `c` where the read value must be truly `c` while `c` has not been incremented.
- Each process should be modelled as a separate thread.
- When `c` is incremented over its max storage, it is wrapped around.
- Reads of `c` must be done by individual bytes.
- Writes of `c` must be done by individual bytes.
- Reads and writes of individual bytes are atomic operations.
- Processes should never block.
- No concurrency constructs are to be used (e.g. semaphores, monitors, synchronised methods, `java.util.concurrent.atomic`) except for `volatile`.

### General Requirements

### Reader Process Requirements

- The reader must write `k` times.

### Writer Process Requirements

## Subproblems

- How do we ensure that the counter value, `v`, read by a `reader` process is equal to the shared counter, `c`, while `v` is being read?

## Assumptions

We assume the following:
- `readByByte` and `writeByByte` are atomic functions (despite not being implemented atomically).

- The writer must write `k` times.

## Algorithm

### Formulation



### Implementation

### Transition Diagram

```mermaid
flowchart
    
```

## Promela Verification

### Mutual Exclusion

### Eventual Entry

### Absence of Deadlock

### Absence of Unncessary Delay

### ...

## 