
# Constraint Satisfaction

Without linearity, type unification can proceed by eagerly solving equality constraints into substitutions, thus never having to accumulate constraints.
However we cannot always eagerly solve constraints once we add usage annotations to the inputs and outputs of channels.

## Example

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

## Discussion

Constraints are either between type metavariables or usage annotations (containing both constants and variables).
When a type metavariable is substituted in a constraint, the result can be simplified into constraints between type metavariables or usage annotations.
Constraints result in substitutions, which must then be applied to both the typing context and other constraints.

Constraints on usage annotations form a binary tree where the nodes are metavariables and the leaves are metavariables or constants.
In this tree `0`s can be removed, `omega`s are propagated upwards, and constants can be added up.

Sound constraint solving for `x = y + z` has the signature `forall xyz. Maybe (exists subst. exists constrs. [[ constrs ]] -> subst <| x = subst <| y + subst <| z)`.
That is, a context split constraint can be satisfied if there exists a substitution `subst` and some new constraints `constrs` such that if those new constraints `constrs` are satisfied, then substituting `subst` in `x`, `y` and `z` pointwise satisfies the constraint. `x = y + z` `x = y + z` `x = y + z`
