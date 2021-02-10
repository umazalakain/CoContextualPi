---
title: Syntax, Metavariables and Unification with de Bruijn Indices
author: Uma Zalakain
---

# Previously, in Typing Process Calculi...

- Defined a syntax of the pi calculus
- Defined a reduction semantics
- Defined a type system with shared/graded/linear types
- Showed (in Agda) that reduction preserves well-typedness
- TODO: provide decidable type checking, i.e.
  ```
  ∀ (Γ : Ctx) (P : Proc) → Γ ⊢ P ⊎ ¬ Γ ⊢ P
  ```

# How do we infer type annotations?

```
server := succ?(n, y) . y!(n+1) . server
client := new a in (succ!(39, a) || a?(z) . print!(z))
system := server || client
```

How do we use the usages of channels to infer their types?

```
succ  : #[ω,1] (int × #[0,1] int)
print : #[0,1] int
a     : #[1,1] int
```

# The Language

- Algebra of processes.
- Expression language with sums and products.
- TODO: recursion/replication.
- TODO: linearity.
- TODO: (limited form of) polymorphism.

# Co-Contextual Type Inference

- Collects usage requirements bottom up.

- Intrinsic proof of soundness: inference returns a derivation.

- On expressions:
  ```
  infer : (e : Expr) → Maybe (∃t. ∃Γ. Γ ⊢ e ∶ t)
  ```
  Given an expression `e`, try to infer a context `Γ` and a type `t` such that `Γ ⊢ e : t`.

- On processes:
  ```
  infer : (P : Proc) → Maybe (∃Γ. Γ ⊢ P)
  ```
  Given a process `P`, try to infer a context `Γ` such that `Γ ⊢ P`.
  
- Type checking `Γ ⊢ P` means deciding whether `infer P = just Δ` and `Γ ⊆ Δ`.

- TODO: show that type inference is complete, i.e.
  ```
  ∀ (Γ : Ctx) (P : Proc) → Γ ⊢ P → infer P = just Δ × Γ ⊆ Δ
  ```

# Merging Contexts

On parallel composition `P || Q`:

1. Infer contexts for `P` and `Q` independently.
2. Merge both contexts.

Also occurs on all other constructs.

Adding linearity into the mix entails adding up multiplicities on both sides.

# Merging = Unification

Merging contexts = pointwise unification of types.

On the left:
```
succ!(39, a)

a    :          $l0
succ : # (int × $l0)
```

On the right:
```
a?(z) . print!(z)

z     :   $r0
a     : # $r0
print : # $r0
```

Unify:
```
$l0 == # $r0
```

Substitute `$l0` with `# $ro`:
```
succ  : # (int × # $r0)
a     :          # $r0
print :          # $r0
z     :            $r0
```

# First Order Unification (to be continued)

- We have no need for "unification up to an algebra": we just need to compare multiplicites.
- *First Order Unification by Structural Recursion*, by Conor McBride.
