# HW2 - Dan Nguyen (z5206032)

## No Skip

```promela
byte x = 0;

active proctype P() {
    x = 1;
    x = 2;
    x = 3;
}

ltl skip_2 { <>(x == 1 until x == 3) }
```

Let:
- $\phi \models x == 1$
- $\psi \models x == 3$

The model satisfies `skip_2` because "eventually" there will be a state which satisfies: $\phi \; \mathcal{U} \; \psi$.
I.e. the model can be satisfied if only `x = 1` is true and does not need `x = 3` to be true immediately after `x = 1` is true.

If there was no "eventually", then the model needs to hold true for all states which is obviously not satisfied since `x = 3` is not true immediately after `x = 1` is true.
