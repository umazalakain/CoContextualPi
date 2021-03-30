
# Introduction

Type inference for the pi calculus with linear and shared channel types.
Composite sum and product types.
**TODO: recursion/replication**
**TODO: bounded linear types?**
**TODO: type assertions**

Co-contextual type inference: traverses the syntax bottom up, collecting constraints on the typing context.
Shared types can be eagerly unified and the resulting substitutions applied.
Adding usage annotations to types complicates things: we need to keep track of the fact that `x = y + z`, even if `x`, `y` and `z` are unknowns.
This is true for both usage annotations and types containing usage annotations.
We cannot, thus, solve eagerly.
The solution is to keep these constraints around and defer the solution.
It might even be that some constraints have more than one possible solution.
We cannot confine ourselves to an eager choice.
At the same time, we need to show that the constraints that we postulate are enough to solve the problem.
This gives raise to the following soundness theorem:

```
forall (p : Proc). exists (gamma : Ctx). exists (constraints : List Constraint). forall (omega : Substitution). [[ omega <| constraints ]] -> (omega <| gamma) |- P
```

Some constraints can however be simplified.
In this case, we need to show that the simplified version is enough to entail the original constraints:

```
forall (c : List Constraint). exists (subc : List Constraint). forall (omega : Substitution). [[ omega <| subc ]] -> [[ omega <| c ]]
```

These normalization could in fact be performed eagerly, but we find it is best to separate stages.
The resulting set of normalized constraints has had equality constraints substituted out.
The only constraints left are splits between two type metavariables, splits between two usage metavariables, and splits between a usage constant and a usage metavariable.

### Example Problem

Consider the program `send a <- (); send x <- a; end` that sends a unit across `a`, then sends `a` across `x` and terminates.
Cocontextual type inference traverses the program bottom up, so we start by inferring the context requirements for `end`:

```
end | a : ?0 | x : ?1 | used(?0) | used(?1)
```

For all `t`, `used(t)` ensures that `t` has no unused linear usage annotations left, and desugars to the following:

```
end | a : ?0 | x : ?1 | ?0 = ?0 + ?0 | ?1 = ?1 + ?1
```

It is already the case that we cannot solve these constraints, so we need to keep them around.
Let's now consider the next step `send x <- a`, which is typed as follows:

```
A = B + C
C = D + E
B |- x : #01 t
D |- a : t
E |- P
---------------
send x <- a ; P
```

We learn that `x` must be a channel, that it must be *at least* capable of sending some part `?1` of `a`, and that after sending that it we must be left with `?1`, which satisfies the `used` predicate.
At the same time, `a` must be something such that after having some part `?2` sent over `x`, it must be left with `?0`, which also satisfies the `used` predicate.

```
send x <- a | a : ?3 | x : ?4 | ?0 = ?0 + ?0 | ?1 = ?1 + ?1 | ?3 = ?2 + ?0 | ?4 = #01 ?2 + ?1
end         | a : ?0 | x : ?1 | ?0 = ?0 + ?0 | ?1 = ?1 + ?1
```

The last constraint `#?4 = #01 ?2 + ?1` can be simplified because we now know that `?4` and `?1` must be a channel.
The result of this constraint is a substitutions `?4 |-> #?xi?xo ?2` and `?1 |-> #?xi'?xo' ?2` for new metavariables `?xi`, `?xo`, `?xi'` and `?xo'`.
We apply this substitution:

```
send x <- a | a : ?3 | x : #?xi?xo ?2 | ?0 = ?0 + ?0 | #?xi'?xo' ?2 = #?xi'?xo' ?2 + #?xi'?xo' ?2 | ?3 = ?2 + ?0 | #?xi?xo ?2 = #01 ?2 + #?xi'?xo' ?2
```

We can now simplify the constraints pointwise:

```
send x <- a | a : ?3 | x : #?xi?xo ?2 | ?0 = ?0 + ?0 | ?xi' = ?xi' + ?xi' | ?xo' = ?xo' + ?xo' | ?3 = ?2 + ?0 | ?xi = 0 + ?xi' | ?xo = 1 + ?xo'
```

Let's now continue to the step `send a <- ()`:

```
send a <- () | a : ?5 | x : #?xi?xo ?2 | ?0 = ?0 + ?0 | ?xi' = ?xi' + ?xi' | ?xo' = ?xo' + ?xo' | ?3 = ?2 + ?0 | ?xi = 0 + ?xi' | ?xo = 1 + ?xo' | ?5 = #01 Unit + ?3
send x <- a  | a : ?3 | x : #?xi?xo ?2 | ?0 = ?0 + ?0 | ?xi' = ?xi' + ?xi' | ?xo' = ?xo' + ?xo' | ?3 = ?2 + ?0 | ?xi = 0 + ?xi' | ?xo = 1 + ?xo'
```

As before, `?5 = #01 Unit + ?3` results in substitutions `?5 |-> #?ai?ao Unit` and `?3 |-> #?ai'?ao' Unit`:

```
send a <- () | a : #?ai?ao Unit | x : #?xi?xo ?2 | ?0 = ?0 + ?0 | ?xi' = ?xi' + ?xi' | ?xo' = ?xo' + ?xo' | #?ai'?ao' Unit = ?2 + ?0 | ?xi = 0 + ?xi' | ?xo = 1 + ?xo' | #?ai?ao Unit = #01 Unit + #?ai'?ao' Unit
```

From the constraint `#?ai'?ao' Unit = ?2 + ?0` we learn that `?2 |-> #?ai''?ao'' Unit` and `?0 |-> #?ai'''?ao''' Unit`:

```
send a <- () | a : #?ai?ao Unit | x : #?xi?xo (#?ai''?ao'' Unit) | #?ai'''?ao''' Unit = #?ai'''?ao''' Unit  + #?ai'''?ao''' Unit  | ?xi' = ?xi' + ?xi' | ?xo' = ?xo' + ?xo' | #?ai'?ao' Unit = #?ai''?ao'' Unit + #?ai'''?ao''' Unit | ?xi = 0 + ?xi' | ?xo = 1 + ?xo' | #?ai?ao Unit = #01 Unit + #?ai'?ao' Unit
```

We simplify constraints pointwise:

```
send a <- () | a : #?ai?ao Unit | x : #?xi?xo (#?ai''?ao'' Unit) | ?ai''' = ?ai''' + ?ai''' | ?ao''' = ?ao''' + ?ao''' | ?xi' = ?xi' + ?xi' | ?xo' = ?xo' + ?xo' | ?ai' = ?ai'' + ?ai''' | ?ao' = ?ao'' + ?ao'''  | ?xi = 0 + ?xi' | ?xo = 1 + ?xo' | ?ai = 0 + ?ai' | ?ao = 1 + ?ao'
```

For clarity, we can arrange the multiplicity constraints in binary trees:

```
?ai = 0 + (?ai'' + ?ai''')
?ao = 1 + (?ao'' + ?ao''')
?xi = 0 + ?xi'
?xo = 1 + ?xo'
```

Since we came to the end of inference and we know that `?ai'''`, `?ao'''`, `?xi'` and `?xo'` must satisfy `used`, we instantiate them to the lowest usage annotation that satisfies that predicate, i.e. `0`

```
?ai = 0 + (?ai'' + 0)
?ao = 1 + (?ao'' + 0)
?xi = 0 + 0
?xo = 1 + 0
```

This is now monoid solving:

```
?ai = ?ai''
?ao = 1 + ?ao''
?xi = 0
?xo = 1
```

Giving raise to:

```
send a <- (); send x <- a; end | a : #?ai''(1 + ?ao'') Unit | x : #01 (#?ai''(1 + ?ao'') Unit)
```

Which is open term polymorphic on the multiplicities `?ai''` and `?ao''` of `a` that are sent over `x`.

## Type System

The type system is the usual standard type system based on context splits that one defines for the pi calculus.
Usage annotations are `0`, `1`, `omega`.
Context splits are defined as follows:

```
x     = x + 0
x     = 0 + x
omega = y + z
```

Only the usage annotations at the upper level of a channel type are split: the usage annotations of any channel type that is send as data are preserved on all three sides of the split.

## Constraint Satisfaction

Constraints are defined as either equality constraints `S == T`, or usage splits `S == T + R`.
The `[[_]]` function interprets them into their type counterparts `S \equiv T` and `S := T + R`.
Substituting into a constraint substitutes pointwise. 
