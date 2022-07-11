# HW3 - Dan Nguyen (z5206032)

## Manna-Pnueli Algorithm

Consider the Manna-Pneuli algorithm where $p_{2}$ and $q_{2}$ are **not** a single atomic step.:
```
int wantp, wantq = 0, 0
```

Process $P$:
```
    forever do
p1      non-critical section
p2      if wantq == -1
p3          wantp = -1
p4      else
p5          wantp = 1
p6      await wantq != wantp
p7      critical section
p8      wantp = 0
```

Process $Q$:
```
    forever do
q1      non-critical section
q2      if wantp = -1
q3          wantq = 1
q4      else
q5          wantq = -1
q6      await wantq != -wantp
q7      critical section
q8      wantq = 0
```

Using the LTL model:
$$
\text{mutex} \models \Box \neg(p_{7} \land q_{7})
$$

The model was verified to be violatable thrice using the following spin command:
```
spin -search -c0 -e -ltl mutex manna_pneuli_no_atomic.pml
```

### Trail 1

Running the trail:
```
spin -p -s -r -X -v -l -g -k manna_pneuli_no_atomic.pml1.trail manna_pneuli_no_atomic.pml
```

Trail 1 fails due to an interleaving of:
$$
\begin{matrix}
\text{step} & p & q & \text{wantp} & \text{wantq} \\
\hline
54 & - & q_{5} & 0 & 0 \\
56 & - & q_{6} & 0 & -1 \\
58 & p_{5} & - & 0 & -1 \\
60 & p_{6} & - & 1 & -1 \\
\hdashline
& p_{7} & q_{7} & 1 & -1 \\
\end{matrix}
$$

### Trail 2

Running the trail:
```
spin -p -s -r -X -v -l -g -k manna_pneuli_no_atomic.pml2.trail manna_pneuli_no_atomic.pml
```

Trail 2 fails due to an interleaving of:

$$
\begin{matrix}
\text{step} & p & q & \text{wantp} & \text{wantq} \\
\hline
70 & p_{5} & - & 0 & 0 \\
72 & p_{6} & - & 1 & 0 \\
74 & - & q_{3} & 1 & 0 \\
76 & - & q_{6} & 1 & 1 \\
\hdashline
& p_{7} & q_{7} & 1 & 1 \\
\end{matrix}
$$

### Trail 3

Running the trail:
```
spin -p -s -r -X -v -l -g -k manna_pneuli_no_atomic.pml3.trail manna_pneuli_no_atomic.pml
```

Trail 3 fails due to an interleaving of:

$$
\begin{matrix}
\text{step} & p & q & \text{wantp} & \text{wantq} \\
\hline
50 & p_{3} & - & 0 & 0 \\
52 & p_{6} & - & -1 & 0 \\
54 & - & q_{5} & -1 & 0 \\
56 & - & q_{6} & -1 & -1 \\
\hdashline
& p_{7} & q_{7} & & \\
\end{matrix}
$$

## Szymanski's Algorithm




## Composing Solutions

```
shared vars of A
shared vars of B
```

Process $C$:
```
    forever do
p1      non-critical section
p2      entry protocol of A
p3      entry protocol of B
p4      critical section
p5      exit protocol of B
p6      exit protocol of C
```

### Part A

> If either $A$ or $B$ satisfies mutual exclusion, then $C$ satisfies mutual exclusion.


### Part B

> If $A$ has no unnecessary delay and $B$ satisfies mutual exclusion then $C$ has no unnecessary delay.

### Part C

> If $A$ satisfies mutual exclusion and $B$ has no unnecessary delay then $C$ has no unncessary delay.

### Part D

> If $A$ is deadlock free and $B$ guarantees eventual entry then $C$ guarantees eventual entry.