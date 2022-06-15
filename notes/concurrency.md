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
- $\phi \models \phi \; \mathcal{U} \; \psi \iff \exists i \text{ s.t. } \sigma|_{i} \models \psi \text{ and } \forall j < i, \; \sigma|_{j} \models \phi$

> $\sigma|_{n}$ denotes the suffix of $\sigma$ starting at $n + 1$ i.e. drops the first $n$ states.

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
