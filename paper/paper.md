
# Introduction

Type inference for the pi calculus with linear and shared channel types.

**TODO: recursion/replication**
**TODO: bounded linear types?**
**TODO: type assertions**

Consider a $\pi$-calculus with usage annotations on channels.
These usage annotations are one of $0$, $1$, or $\omega$.
$0$ must not be used, $1$ must be used exactly once, $\omega$ can be used as many times as desired.
Sum and products contain usage annotations on their leafs.

## Types

Let $\gamma$ be a context of metavariable kinds, where a kind is either a `type` or a `usage`.
Then $\gamma \ni k$ is a choice of a $k$ inside $\gamma$.
$$
\begin{aligned}
S, T : \texttt{Type}~\gamma &= \texttt{mvar}~(\gamma \ni \texttt{type}) ~|~ \#_{i,o}t ~|~ \top ~|~ S + T ~|~ S \times T \\
i,o : \texttt{Usage}~\gamma &= \texttt{mvar}~(\gamma \ni \texttt{usage}) ~|~ 0\cdot ~|~ 1\cdot ~|~ \omega\cdot
\end{aligned}
$$

## Type System


The type system is the usual standard type system based on context splits that one defines for the pi calculus.
TODO: insert type system definition here:.

Usage annotations are $0\cdot$, $1\cdot$, $\omega\cdot$.
Context splits are defined as follows:

$$
\begin{aligned}
\forall x.    && x           &= x + 0\cdot \\
\forall x.    && x           &= 0\cdot + x \\
\forall x ~y. && \omega\cdot &= y + z
\end{aligned}
$$

Only the usage annotations at the upper level of a channel type are split: the usage annotations of any channel type that is send as data are preserved on all three sides of the split.

# Inference

Co-contextual type inference: traverses the syntax bottom up, collecting constraints on the typing context.

Constraints can be of the following form:

- $S = T$: types $S$ and $T$ must be unifiable.
- $S = T + R$: adding up the usage annotations in $T$ and $R$ must result in $S$.

Constraints of the form $S = T$ can always be eagerly unified.
However constraints of the form $S = T + R$ might contain variables: $\texttt{mvar}~x = \texttt{mvar}~y + \texttt{mvar}~z$.
In an open process, these variables cannot safely be instantiated to $0$.
As such, no substitution is possible, yet we need to remember the constraint.
(It might also be that some constraints have more than one possible solution.)
At the same time, we need to show that the constraints that we postulate are enough to solve the problem.

\paragraph{Constraint Satisfaction}
The $[\![\_]\!]$ function interprets constraints into their type counterparts $S \equiv T$ and $S = T + R$.
Substituting into a constraint substitutes pointwise. 

\paragraph{Inference}
$$
\texttt{infer} : \forall (p : \texttt{Proc}~n). ~ \exists \gamma. ~ \texttt{Ctx}~n~\gamma \times \texttt{List}~(\texttt{Constr}~\gamma)
$$

\paragraph{Inference soundness.} Every substitution $\sigma$ that makes the constraints hold will make the process typable under the substituted context.
$$
\begin{aligned}
\texttt{infer-sound} &: \forall (p : \texttt{Proc}~n). ~ \texttt{infer}~P \equiv \gamma , \Gamma , cs \\
&\to \forall (\sigma : \texttt{Subst}~\gamma~\delta). ~ [\![ \sigma \triangleleft cs ]\!] \\
&\to (\sigma \triangleleft \Gamma) \vdash P
\end{aligned}
$$

\paragraph{Inference completeness.} For every context $\Delta$ that makes the process typable there exists a most general substitution $\sigma$ that will solve the constraints and which substitutes in $\Gamma$ to something more general than $\Delta$.
$$
\begin{aligned}
\texttt{infer-complete} &: \forall (p : \texttt{Proc}~n). ~ \texttt{infer}~P \equiv \gamma , \Gamma , cs \\
&\to \forall (\Delta : \texttt{Ctx}~n~\gamma). ~ \Delta \vdash P \\
&\to \exists \delta. ~ \exists (\sigma : \texttt{Subst}~\gamma~\delta). \\
&\to [\![ \sigma \triangleleft cs ]\!] \times \Delta \subseteq (\sigma \triangleleft \Gamma)
\end{aligned}
$$
where
$$
\Delta \subseteq \Gamma \triangleq \exists \delta. ~ \exists (\sigma : \texttt{Subst} \_ \delta). ~ \Delta \equiv (\sigma \triangleleft \Gamma)
$$

# Constraint Resolution

\paragraph{Constraint Resolution.} Given a set of accumulated substitutions and some constraints, we will return (hopefully) some further substitutions, and a set of leftover constraints to which the substitutions have been applied.
These leftover constraints can either not be simplified or are unsatisfiable.
$$
\begin{aligned}
\texttt{solve} &: \texttt{Subst}~\gamma~\delta \times \texttt{List}~(\texttt{Constr}~\delta) \\
&\to \texttt{Subst}~\gamma~\phi \times \texttt{List}~(\texttt{Constr}~\phi)
\end{aligned}
$$

\paragraph{Soundness.} The simplified constraints are enough to entail the original constraints.
$$
\begin{aligned}
\texttt{solve-sound}
&: \texttt{solve}~(\sigma_1, cs_1) \equiv (\sigma_2, cs_2) \\
&\to \forall (\sigma_f : \texttt{Subst}~\gamma~\delta) \\
& \to [\![ \sigma_f \triangleleft cs_2 ]\!] \to [\![ \sigma_f \cdot \sigma_2 \triangleleft cs_1 ]\!]
\end{aligned}
$$


\paragraph{Completeness.} Any substitution $\sigma_f$ that makes the original constraints $cs_1$ hold will be a specialisation $\sigma_f$ of our returned substitution $\sigma_2$.
The specialisation $\sigma_g$ will make the returned constraints $cs_2$ hold.
$$
\begin{aligned}
\texttt{solve-sound}
&: \texttt{solve}~(\sigma_1, cs_1) \equiv (\sigma_2, cs_2) \\
&\to \forall (\sigma_f : \texttt{Subst}~\gamma~\delta). ~ [\![ \sigma_f \triangleleft cs_1 ]\!] \\
&\to \exists (\sigma_g : \sigma_f = \sigma_g \cdot \sigma_2) \times [\![ \sigma_g \triangleleft cs_2 ]\!]
\end{aligned}
$$


\paragraph{Progress.} Nothing prevents us from returning the original constraints as output.
We therefore promise that every constraint we return is either currently unsolvable because we have not enough information, or is unsatisfiable altogether.
$$
\begin{aligned}
\texttt{solve-sound}
&: \texttt{solve}~(\sigma_1, cs_1) \equiv (\sigma_2, cs_2) \\
&\to \forall c \in cs_2. ~ \texttt{IsDeferred}~c \uplus \texttt{IsUnsat}~c
\end{aligned}
$$
where
$$
\texttt{IsUnsat}~c = \forall \sigma. ~ \neg [\![ \sigma \triangleleft c ]\!]
$$

\paragraph{Instantiation.} 
$$
\forall c. ~ \texttt{IsDeferred}~c \to \exists \sigma. [\![ \sigma \triangleleft c ]\!]
$$


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
