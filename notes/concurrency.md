# Concurrency

Concurrency is an abstraction allowing programs to be structured as multiple processes.

## Symbols

- $\cap$ : and
- $\cup$ : or
- $\implies$ : implies
- $\oplus$ : exlusive or
- $\top$ : truth
- $\bot$ : falsity
- $\llbracket P \rrbracket$ : semantics of $P$ (a program)
- $\models$ : models, entails
- $\circ$ : function composition

## 3 R's

1. Reading concurrent code and programming idioms in a variet of execution contexts.
1. wRiting concurrent software using various abstractions for synchronisation.
1. Reasoning about concurrent systems with formal proof and automatic analysis tools.

## Process Models

Multithreaded process model:

![multithreaded-process-model](multithreaded-process-model.drawio.svg)

Parallel multiprocess model:

![parallel-multiprocess-model](parallel-multiprocess-model.drawio.svg)

Parallel distributed multiprocess model:

![parallel-distributed-multiprocess-model](parallel-distributed-multiprocess-model.drawio.svg)

## Sequential Program

A sequential program consists of a sequence of actions which are completed in total order.

![sequential-program](sequential-program.drawio.svg)

Sequential program reasoning can be represented by the Hoare logic:
$$
\{\phi\}P\{\psi\}
$$

Where:
- $\phi$ is the set of pre-conditions.
- $P$ is the program.
- $\psi$ is the set of post-conditions.

> Program $\left(P\right)$ is a piece of text.

## Dining Cryptographers Problem

Consider the dining cryptographers problem where the cryptographers, $C_{1}, C_{2}, C_{3}$, determines if their dinner was paid for anonymously by either one of the three cryptographers or the NSA:
- Each $C_{i}$ tosses a coin, $t_{i}$.
- Each $C_{i}$ tells what they tossed only to their right.
- Each $C_{i}$ announces (if they paid), if the two coin tosses are "equal" or "different" unless they did not pay then they announce the opposite.
- If there is an even number of "different" announcements, $a_{i}$, then the NSA paid.
- If there is an odd number of "different" announcements then one of $C_{i}$ paid.

Claim:
$$
a_{1} \oplus a_{2} \oplus a_{3} = \top \iff \text{ there's an odd number of diffs}
$$

Test:
$$
\begin{aligned}
\bot \oplus \bot \oplus \bot &= \bot \oplus \bot = \bot \text{ for no diffs} \\
\top \oplus \top \oplus \top &= \bot \oplus \top = \top \text{ for one diff}
\end{aligned}
$$

Define the announcements in terms of the tosses:
$$
\begin{aligned}
a_{1} \oplus a_{2} \oplus a_{3} &= (t_{1} \oplus t_{3}) \oplus (t_{2} \oplus t_{1}) \oplus (t_{3} \oplus t_{2}) \\
&= (t_{1} \oplus t_{2} \oplus t_{3}) \oplus (t_{1} \oplus t_{2} \oplus t_{3}) \\
&= \bot
\end{aligned}
$$

It is clear to see that if one of $C_{i}$ paid then they must lie which negates their announcement and thus the result. Otherwise the NSA paid.

## Concurrent Program

A concurrent program consists of a series of actions which are completed in partial order.

![concurrent-program](concurrent-program.drawio.svg)

> Don't care about what our process models look like because concurrency is an abstraction.

## Interleaving

Partial order is achieved by interleavings.

Interleavings are a logical device that makes it possible to analyse the correctness of concurrent programs.

Interleavings gives rise to a "behaviour".

> Basic problem of concurrent programming is identifying which activities may be done concurrently.

---

Suppose $P = \{ P_{1}, P_{2} \}$. $P$ executes any one of the execution sequences that can be obtained by interleaving the execution sequences of $P_{1}$ and $P_{2}$.
    
Consider any instructions $I_{1}$ and $I_{2}$ from $P_{1}$ and $P_{2}$ respectively.

If $I_{1}$ and $I_{2}$ do not access the same memory cell then it does not matter the order of execution of $I_{1}$ and $I_{2}$.

Suppose $I_{1}$ and $I_{2}$ do writes to the same memory cell, $M$. If $I_{1}$ and $I_{2}$ executed simultaneously then the result is consistent i.e. $M$ will contains either $I_{1}$'s value or $I_{2}$'s value and $M$ does not contain any other value. If $M$ contains $I_{1}$'s value then this is equivalent to saying $I_{1}$ occurred before $I_{2}$ in an interleaving and vice versa.

If the above is not true then it would be impossible to reason about concurrent programs.

---

> Concurrent programs are non-deterministic as there are multiple possible interleavings.

### Synchronisation

Processes need to communicate to organise and coordinate actions.

The red arrows in the concurrent program diagram are synchronisations.

Types of communication:
- Shared Variables: Typically on single-computer execution models.
- Message-Passing: Typically on distributed execution models.

## Behaviour

Behaviour is an infinite sequence of states.

$\Sigma^{\omega}$ captures the set of all behaviours.

> $\Sigma$ is a state.

## Semantics

Semantics $\left(\llbracket P \rrbracket\right)$ of a program is a set of behaviours.

Hoare logic does not work for concurrent programs because they cannot rely on pre-conditions and post-conditions, require intermediate states, and may not terminate.

It is better to reason concurrent programs by defining $\llbracket P \rrbracket$ as the set of all possible behaviours from all different available interleavings of actions.

## Models

Models are used to give semantics to logic e.g.:
$$
\begin{aligned}
\overbrace{\mathcal{V}}^{\text{model}} \models \overbrace{\rho}^{\text{logic}} &\iff \overbrace{\rho \in \mathcal{V}}^{\text{semantics}} \\
\mathcal{V} \models \phi \land \psi &\iff \mathcal{V} \models \phi \text{ and } \mathcal{V} \models \psi \\
\end{aligned}
$$

## Internal vs External State

We sometimes want to hide states.

If we abstract away all internal states, actions that only affect internal states will appear not to change the state at all.

> Stuttering is a finite repetition of the same state.

## Cantor's Uncountability Argument

It is impossible to enumerate the space of all behaviours.

> Uncountable means no bijection between sets of properties and the set of natural numbers ($\implies$ something is infinite).

## Limits

To address Cantor's uncountability argument, we just make finite observations.

The limit closure of $A$ i.e. $\overline{A}$ is the set of all behaviours that are indistinguishable from a behaviour in $A$ if finite observations are made.

The limit closure of $A$ i.e. $\overline{A}$ is the smallest closed set containing $A$, which is also the intersection of all closed sets containing $A$.

$$
A \subseteq \overline{A}
$$

The limit closure of a set $A \subseteq \Sigma^{\omega} = \overline{A}$ where:
$$
\overline{A} = \left\{
    \begin{aligned}
    \sigma &\in \Sigma^{\omega} | \forall n \in \mathbb{N} \\
    \exists \sigma' &\in A \\
    \left. \sigma \right|_{n} &= \left. \sigma' \right|_{n}
    \end{aligned}
    \right\}
$$

> $\left. \sigma \right|_{k}$ denotes the prefix of the behaviour, $\sigma$, for the first $k$ states.

> Set $A$ of behaviours is limit closed if $\overline{A} = A$.

> Set $A$ is dense if $\overline{A} = \Sigma^{\omega}$ i.e. the closure is the space of all behaviours.

### Example 1

$$
\overline{\emptyset} = \emptyset
$$

### Example 2

Let $\Sigma = \{0, 1\}$, and let $A$ be the set of all behaviours that start with a finite number of 0's; followed by infinitely many 1's. What is $\overline{A}$?

If:
$$
A = \left(\overbrace{0, ...}^{0 \text{ to } k \text{ times}}, \overbrace{1, ...}^{\infin \text{ times}}\right)
$$

Then:
$$
\overline{A} = \left\{\overbrace{0, ...}^{0 \text{ to } \infin \text{ times}}, \overbrace{1, ...}^{\infin \text{ times}}\right\}
$$

## Property

A property $\left(A\right)$ of a program is a set of behaviours:
$$
\llbracket P \rrbracket \subseteq A
$$

> The above works for correctness properties but not for security or real-time properties.

We specify systems with *temporal properties* to achieve the above by using either *safety* or *liveness* properties.

### Safety Property

A safety property states that something will **never** happen.

> It can be violated.

Safety properties are limit closed.

---
Let $P$ be a safety property.

Assume $\exists$ a behaviour $\sigma_{\omega} \in \overline{P}$ s.t. $\sigma_{\omega} \notin P$. For $\sigma_{\omega}$ to violate $P$, there must be a specific violating state in $\sigma_{\omega}$ i.e. $\exists k$ where $\sigma_{\omega}|_{k} \notin P$.

Since $\sigma_{\omega} \in \overline{P}$, there must be a behaviour $\sigma \in P$ s.t. $\sigma_{\omega}|_{k} = \sigma|_{k}$.

Thus $\sigma$ both violates and satisfies the property $P$.

---

### Liveness Property

A liveness property states that something will **eventually** happen.

> It cannot be violated.

Liveness properties are dense.

---

Let $P$ be a liveness property.

If $\sigma \in P$, then $\sigma \in \overline{P} \because P \subseteq \overline{P}$.

If $\sigma \notin P$, then $\nexists k$ where $\sigma|_{k} \in P$. However, every finite prefix $\sigma|_{i} \subseteq \sigma$ could be extended differently with some $\rho_{i}$ s.t. $\sigma|_{i\rho_{i}} \in P$. Therefore, $\sigma \in \overline{P}$.

---

## Alpern and Schneider's Theorem

Every property is the intersection of a safety and a liveness property.

---

$$
\begin{aligned}
P &= \overbrace{\overline{P}}^{\text{closed}} \cap \overbrace{\Sigma^{\omega} \setminus (\overline{P} \setminus P)}^{\text{dense}} \\
&=  \overline{P} \cap \Sigma_{\omega} \setminus (\overline{P} \cap P^{c}) \\
&=  \overline{P} \cap \Sigma_{\omega} \cap (\overline{P} \cap P^{c})^{c} \\
&=  \overline{P} \cap \Sigma_{\omega} \cap (\overline{P}^{c} \cup P) \\
&=  \overline{P} \cap (\overline{P}^{c} \cup P) \\
&=  (\overline{P} \cap \overline{P}^{c}) \cup (\overline{P} \cap P) \\
&= \overline{P} \cap P \\
&= P \because P \subseteq \overline{P} \\
\end{aligned}
$$

---

Theorem gives separation of concerns and allows different proof techniques to be used:
- Concurrent program suggests correct actions (safety).
- Scheduler chooses which actions to take (liveness).

### Example 1

The program will stay in state $s_{1}$ for a while then go to state $s_{2}$ forever.

- Safety: $s_{2}$ will never occur before $s_{1}$.
- Liveness: $s_{1}$ will eventually transition to $s_{2}$.

### Example 2

The program will allocate exactly 100 MB of memory.

- Safety: The program allocates exactly 100 MB of memory.
- Liveness: The program will eventually allocate memory.

### Example 3

If given an invalid input, the program will return the value -1.

- Safety: Program returns -1 after seeing an invalid input.
- Liveness: Program after seeing an invalid input, it will eventually return something.

## Linear Temporal Logic

Linear temporal logic (LTL) describes linear time properties and is able to describe behaviours.
 
> Propositional logic describes boolean expressions.

### Syntax

Normal propositional operators:
- $\rho \in \mathcal{P}$ is an LTL formula.
- If $\phi, \psi$ are LTL formulae, then $\phi \land \psi$ is an LTL formula.
- If $\phi$ is an LTL formula, $\neg \phi$ is an LTL formula.

Modal (temporal) operators:
- If $\phi$ is an LTL formula, then $\bigcirc \phi$ is an LTL formula.
- If $\phi, \psi$ are LTL formulae, then $\phi \; \mathcal{U} \; \psi$ is an LTL formula.

> $\bigcirc \phi$ : In the next state, $\phi$ holds.

> $\phi \; \mathcal{U} \; \psi$ :  $\phi$ will hold for a finite amount of states; then, $\psi$ will hold after that.

### Semantics

LTL models are behaviours:
- $\sigma \models \rho \iff \rho \in \sigma_{0}$
- $\sigma \models \rho \land \psi \iff \sigma \models \phi \text{ and } \sigma \models \psi$
- $\sigma \models \neg \phi \iff \sigma \not\models \phi$
- $\sigma \models \bigcirc \phi \iff \sigma|_{1} \models \phi$
- $\sigma \models \phi \; \mathcal{U} \; \psi \iff \exists i \text{ s.t. } \sigma|_{i} \models \psi \text{ and } \forall j < i, \; \sigma|_{j} \models \phi$

> $\sigma|_{n}$ denotes the suffix of $\sigma$ starting at $n + 1$ i.e. drops the first $n$ states. It does not note the prefix, we can tell the difference based on context that this is modelling.

> Propositional logic models were sets of propositional atoms.

> $\Diamond \phi = \top \; \mathcal{U} \; \phi $ : $\phi$ will eventually be true at some point.

> $\Box \phi = \neg(\Diamond(\neg \phi))$ : $\phi$ will always be true from now on.

LTL cannot express branching-time properties. <!-- Explain this? -->

#### Proof 1

Prove:
$$
\Box \phi = \neg (\Diamond \neg \phi)
$$

Consider:
$$
\sigma \models \phi \iff \sigma \models \psi
$$

Proof:
$$
\begin{aligned}
\sigma \models \neg(\Diamond \neg \phi) &= \neg (\sigma \models \Diamond \neg \phi) \\
&= \neg (\exists i. \; \sigma|_{i} \models \neg \phi) \\
&= \neg (\exists i. \; \neg(\sigma|_{i} \models \phi)) \\
&= \forall i. \; \neg \neg(\sigma|_{i} \models \phi) \\
&= \forall i. \; \sigma|_{i} \models \phi \\
&= \Box \phi \\
\end{aligned}
$$

> Note that we use two layers of logic for our proof i.e. metalogic ($\forall, \exists, ...$) and object logic ($\Diamond, \Box, ...$).

#### Proof 2

Prove:
$$
\Box(\phi \land \psi) = \Box\phi \land \Box\psi
$$

Proof:
$$
\begin{aligned}
\sigma \models \Box(\phi \land \psi) &= \forall i. \; \sigma|_{i} \models \phi \land \psi \\
&= \forall i. \; ((\sigma|_{i} \models \phi) \land (\sigma|_{i} \models \psi)) \\
&= (\forall i. \; \sigma|_{i} \models \phi) \land (\forall i. \; \sigma|_{i} \models \psi) \\
&= \sigma \models \Box\phi \land \sigma \models \Box\psi \\
&= \sigma \models \Box\phi \land \Box\psi \\
\end{aligned}
$$

> $\Box\Diamond\phi$ : infinitely often, always eventually.

> $\Diamond\Box\phi$ : almost globally, always true from some point onwards, eventually reach a state where its always true.

## Why Concurrency?

How many scenarios are there for a program with $n$ finite processes consisting of $m$ atomic actions each?

$$
\frac{(nm)!}{m!^{n}}
$$

For 6 processes consisting of 6 sequential atomic actions each, there are 2 670 177 736 637 149 247 308 800 scenarios...

It is infeasible to test all possible scenarios so we apply *formal methods*.

## Model Checking

Given a program, $P$, and property, $\phi$, exhaustingly searches the state-space for a counter-example to $\phi$.

Pros:
- Easy to use push-button technology.
- Instructive counter-examples (error traces) help debugging.

Cons:
- State explosion problem (infeasible to model check in reasonable time).

> Not learning how to write a model checker in this course. Just how to use one i.e. Promela.

## Theorem Proving

Construct a (formal) proof for $P$.

Pros:
- No (theoretical) limits on state-spaces.
- Can learn why theorem holds.

Cons:
- Requires expert users to hand-crank thorough proofs.

## Promela

### Volatile Variables

Sometimes we cannot guarantee that a statement is executed atomically (i.e. in one step). This is statement is called the *limit critical reference restriction*.

We require each statement to only access at most one shared variable at a time to overcome volatile variables.

In the following example, each statement, access a single variable:
```promela
do
:: i < 10 ->
    temp = c;
    c = temp + 1;
od
```

### Ensuring Atomicity

Grouping statements with `atomic` prevents them from being interrupted:
```promela
atomic {
    run P();
    run P();
}
```
If a statement in the atomic block is blocked, then atomicity is temporarily suspended and another process may run

Grouping statements with `d_step` is more efficient than `atomic` because it groups them into a single transition:
```promela

```
<!-- TODO -->
If a statement in the d_step block is blocked, then runtime error is raied. `if` and `do` is not allowed.

> `d_step` stands for deterministic step.

## Atomicity

Critical section problems tend to look like this (in the real world):

```
forever do
    non-critical section
    pre-protocol
    critical section
    post-protocol
```

Non-critical section models the possibility that a process may do something else (maybe taking a finite or infinite amount of time).

We want to find pre- and post-protocols such that certain **atomicity properties** are satisfied:
- **Mutual Exclusion** (safety): No two properties are in the critical section at the same time.
- **Eventual Entry** (liveness): Process will eventually be able to execute its critical section (once entering pre-protocol).
- **Absence of Deadlock** (safety): System should never reach a state where there are no actions.
- **Absence of Unnecessary Delay** (liveness): If only one process is attempting to enter its critical section, it succeeds.

### Dekker's Algorithm

A solution to the mutual exclusion problem and satisfying all the above atomicity properties:

```
forever do
    non-critical section
    wantp = True;            // Flag intent that this process wants to do work.
    while wantq do           // Let other process do work.

        // We have the following block in case both processes are in the while loop.
        // This avoids livelock.
        if turn = 2 then     // If it's their turn.
            wantp = False;   // State that we don't want it.
            await turn = 1;  // Wait until it's our turn.
            wantp = True;    // State that we want it now.
    critical section
    turn = 2;                // Their turn now.
    wantp = False;           // We don't want to go into critical section anymore.
```

## Fairness

Weak fairness for an action, $\pi$:
$$
\Box(\Box\text{enabled}(\pi) \implies \Diamond\text{taken}(\pi))
$$

Strong fairness for an action, $\pi$:
$$
\Box(\Box\Diamond\text{enabled}(\pi) \implies \Diamond\text{taken}(\pi))
$$

## Transition Diagrams

A transition diagram is a tuple:
$$
(L, T, s, t)$$

Where:
- $L$ is a set of locations (program counter values).
- $T$ is a set of transitions.
- $s \in L$ is an entry location.
- $t \in L$ is an exit location.

A transition is expressed as:
$$
l_{i} \xrightarrow{g; f} l_{j}
$$

Where:
- $l_{i}$ and $l_{j}$ are locations.
- $g$ is a guard, $\Sigma \rightarrow \mathbb{B}$.
- $f$ is a state update, $\Sigma \rightarrow \Sigma$.

> For $g; f$, if $g = \top$, then write $f$.

> For $g; f$, if $f$ is identity, then write $g$.

### Example 1

```
l0  i = 0;
l1  s = 0;
l2  while i != N do
        s = s + 1;
l3      i = i + 1;
    od
```

```mermaid
stateDiagram-v2
    [*] --> l0
    l0 --> l1: True. i = 0
    l1 --> l2: s = 0
    l2 --> l3: i != N. s = s + i
    l3 --> l2: i = i + 1
    l2 --> [*]: i = N
```
<!-- TODO UPDATE DIAGRAM -->

## Floyd Verification

Given a transition diagram, $(L, T, s, t)$:
1. Associate each location $l \in L$ with an assertion, $\mathcal{Q}(l): \Sigma \rightarrow \mathbb{B}$.
2. Prove that this assertion network is inductive i.e. for each transition in $T$, $l_{i} \xrightarrow{g; f} l_{j}$, show that:
$$
\mathcal{Q}(l_{i}) \land g \Rightarrow \mathcal{Q}(l_{j}) \circ f
$$

> If annotation at $l_{i}$ is true and guard is true, then after updating the state with $f$, the annotation at $l_{j}$ must be true.

3. Show that $\phi \Rightarrow \mathcal{Q}(s)$ and $\mathcal{Q}(t) \Rightarrow \psi$.

> Annotations are also called an assertion network.

> Floyd's method is a theorem proving technique.

### Example 1

```mermaid
stateDiagram-v2
    [*] --> l0
    l0 --> l1: True. i = 0
    l1 --> l2: s = 0
    l2 --> l3: i != N. s = s + i
    l3 --> l2: i = i + 1
    l2 --> [*]: i = N
```
<!-- TODO UPDATE DIAGRAM -->

Let $P$ be the whole transition diagram.

Prove:
$$
\{\top\}P\{s = \frac{N(N - 1)}{2}\}
$$

Proof is done by finding an "annotation" for every location - annotation should state something that's always true at that location:
- Pre-condition implies the start location's annotation.
- Exit location's annotation implies the post-condition.
- If current location's annotation is true, then if we take a transition, the next location's annotation becomes true.

Proof:
$$
\begin{aligned}
l_{0}&: \top \\
l_{1}&: i = 0 \\
l_{2}&: s = \frac{i(i - 1)}{2} \\
l_{3}&: s = \frac{(i + 1)i}{2} \\
l_{4}&: s = \frac{N(N - 1)}{2} \\
\end{aligned}
$$

Considering $l_{1} \rightarrow l_{2}$, we must prove:
$$
\begin{aligned}
i &= 0 \rightarrow s = \frac{i(i - 1)}{2} \\
\text{Let } s = 0 \text{: } i &= 0 \rightarrow 0 = \frac{i(i - 1)}{2} \\
\end{aligned}
$$

Considering $l_{2} \rightarrow l_{3}$, we must prove:
$$
\begin{aligned}
s = \frac{i(i - 1)}{2} \land i \neq N \rightarrow s + i = \frac{(i + 1)i}{2} \\
\end{aligned}
$$

## Concurrent Transition Diagrams

Given two processes $P$ and $Q$ with transition diagrams $(L_{P}, T_{P}, s_{P}, t_{P})$ and $(L_{Q}, T_{Q}, s_{Q}, t_{Q})$, the parallel composition of $P$ and $Q$, $P \; \| \; Q$, is defined as $(L, T, s, t)$ where:
- $L = L_{P} \times L_{Q}$
- $s = s_{P}s_{Q}$
- $t = t_{P}t_{Q}$
- $p_{i}q_{i} \xrightarrow{g; f} p_{j}q_{i} \in T \text{ if } p_{i} \xrightarrow{g; f} p_{j} \in T_{P}$
- $p_{i}q_{i} \xrightarrow{g; f} p_{i}q_{j} \in T \text{ if } q_{i} \xrightarrow{g; f} q_{j} \in T_{Q}$

![concurrent-transition-diagram](concurrent-transition-diagram.png)

> Every horizontal transition belongs to the horizontal process. Every vertical transition belongs to the vertical process.

Floyd's verification can be applied on basic concurrent programs after taking the parallel composition. However, not feasible because of state-space explosion.

## Owicki-Gries Method

The Owicki-Gries method generalises verifying concurrent programs to $n$ processes, by requiring more interference freedom obligations.

![owicki-gries-transition-diagram](owicki-gries-transition-diagram.png)

To show $\{\phi\} P \; \| \; Q \{\psi\}$:
1. Define local assertion networks $\mathcal{P}$ and $\mathcal{Q}$ for $P$ and $Q$.
2. Show $\mathcal{P}$ and $\mathcal{Q}$ are inductive.
3. For each location $p \in L_{P}$, show that $\mathcal{P}(p)$ is not falsified by any transition of $Q$ i.e.:
$$
\forall q \xrightarrow{g; f} q' \in T_{Q}: \mathcal{P}(p) \land \mathcal{Q}(q) \land g \Rightarrow \mathcal{P}(p) \circ f
$$
4. Do the same for $Q$.
5. Show that $\phi \Rightarrow \mathcal{P}(s_{P}) \land \mathcal{Q}(s_{Q})$ and $\mathcal{P}(t_{P}) \land \mathcal{Q}(t_{Q}) \Rightarrow \psi$.

> Owicki-Gries method is a theorem proving technique.

### Proving Mutual Exclusion

Don't have a post-condition.

Make the assertions at the critical sections contradictory so they cannot be true simultaenously.

Ensure that each transition does not violate limited critical reference rule.

#### Example 1

##### Manna-Pnueli Algorithm

Consider the Manna-Pnueli algorithm:

Initialise:
```
wantp = 0
wantq = 0
```

Process $P$:
```
    forever do
p1      non-critical section
p2      if wantq == -1
            wantp = -1
        else
            wantp = 1
p3      await wantq != wantp
p4      critical section
p5      wantp = 0
```

Process $Q$:
```
    forever do
q1      non-critical section
q2      if wantp == -1
            wantq = 1
        else
            wantq = -1
q3      await wantq != -wantp
q4      critical section
q5      wantq = 0
```

> $p_{2}$ and $q_{2}$ are one atomic step.

##### Check $P$'s annotations are Inductive

Define the annotations for process $P$:
- $p_{1}$: $\text{wantp} = 0$
- $p_{2}$: $\text{wantp} = 0$
- $p_{3}$: $\text{wantp} \neq 0$
- $p_{4}$: $\text{wantp} \neq 0 \land \text{wantq} \neq \text{wantp}$
- $p_{5}$: $\top$

<!-- TODO: induction -->

##### Check $Q$'s annotations are Inductive

Define the annotations for process $Q$:
- $q_{1}$: $\text{wantq} = 0$
- $q_{2}$: $\text{wantq} = 0$
- $q_{3}$: $\text{wantq} \neq 0$
- $q_{4}$: $\text{wantq} \neq 0 \land \text{wantp} \neq -\text{wantq}$
- $q_{5}$: $\top$

<!-- TODO: induction -->

##### Check for Interference

Suppose $P$ is at location $p_{4}$. Then:
$$
\text{wantp} \neq 0 \land \text{wantq} \neq \text{wantp}
$$

Check that $Q$ cannot falsify the above annotation. We only have to consider locations $q_{2}$ and $q_{5}$ since other locations do not have writing annotations.

For $Q$ at location $q_{5}$:
$$
\text{wantp} \neq 0 \land \text{wantq} \neq \text{wantp} \land \top \implies \text{wantp} \neq 0 \land 0 \neq \text{wantp}
$$

For $Q$ at location $q_{2}$:
$$
\text{wantp} \neq 0 \land \text{wantq} \neq \text{wantp} \land \text{wantq} = 0 \land \text{wantp} \neq -1 \implies \text{wantp} \neq 0 \land 1 \neq \text{wantp}
$$

<!-- TODO: prove for each location in P and Q -->

##### Check Mutual Exclusion Holds

Prove the algorithm is mutually exclusive by showing $P$ at location $p_{4}$ and $Q$ at location $q_{4}$ cannot both be true.

<!-- TODO: Proof -->
