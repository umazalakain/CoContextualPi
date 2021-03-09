open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; trans; cong; sym; inspect; [_] )
open import Relation.Nullary using (Dec; yes; no)
open import Category.Functor
open import Category.Monad
open import Category.Applicative

import Data.Maybe.Categorical as maybeCat
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Product as Product using (∃; ∃-syntax; Σ-syntax; _,_)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Sum as Sum using (inj₁; inj₂)
import Data.List.Properties as Listₚ

open import CoContextualPi.Types
open import CoContextualPi.TypeSystem

module CoContextualPi.LinearityUnification where

private
  -- Help ourselves to some goodies
  open RawFunctor {{...}}
  open RawApplicative {{...}} hiding (_<$>_)
  open RawMonad {{...}} hiding (_<$>_; _⊛_)
  instance maybeFunctor = maybeCat.functor
  instance maybeMonad = maybeCat.monad
  instance maybeApplicative = maybeCat.applicative

private
  variable
    n m l : ℕ
    k k' : Kind
    γ δ ξ : KindCtx
    x y z : γ ⊢= k

+ᵤ-<| : {x y z : γ ⊢= multiplicity} (σ : ∀ {k} → γ ∋= k → δ ⊢= k) → x ≔ y + z → (σ <| x) ≔ (σ <| y) + (σ <| z)
+ᵤ-<| σ left = left
+ᵤ-<| σ right = right
+ᵤ-<| σ shared = shared

FSubst : ∀ {p} {γ : KindCtx} → ({δ : KindCtx} → (∀ {k} → γ ∋= k → δ ⊢= k) → Set p) → Set p
FSubst {γ = γ} P = ∃[ δ ] (Σ[ σ ∈ (∀ {k} → γ ∋= k → δ ⊢= k) ] P σ)
syntax FSubst (λ σ → A) = ∃[ σ <| A ]


+-comm : x ≔ y + z → x ≔ z + y
+-comm left = right
+-comm right = left
+-comm shared = shared
+-comm var = var
+-comm top = top
+-comm (chan i o) = chan (+-comm i) (+-comm o)
+-comm (prod l r) = prod (+-comm l) (+-comm r)
+-comm (sum l r) = sum (+-comm l) (+-comm r)

+ᵤ-id-thick : (x : γ ∋= multiplicity ▹ δ) (t : δ ⊢= multiplicity) → t ≔ (0∙ for x <| var (! x)) + t
+ᵤ-id-thick x t
  with refl , eq ← Unificationₚ.thick-nothing x
  rewrite eq = right

erase : γ ⊢= type → (type ∷ γ) ⊢= type
erase (var x) = {!!}
erase (con n as) = {!!}

+-flex : (x : γ ∋= k) (t : γ ⊢= k) → Maybe ∃[ σ <| ∃[ r ] r ≔ (σ <| var x) + (σ <| t) ]
+-flex {k = multiplicity} (! x) (var y) = just (! (0∙ for x) , (0∙ for x) y , +ᵤ-id-thick x ((0∙ for x) y))
+-flex {k = type} x (var y) = just (! |> (Product.map _ suc) , var (! zero) , var )
+-flex (! x) 0∙ = just (! 0∙ for x , 0∙ , +ᵤ-id-thick x 0∙)
+-flex (! x) 1∙ = just (! 0∙ for x , 1∙ , +ᵤ-id-thick x 1∙)
+-flex (! x) ω∙ = just (! 0∙ for x , ω∙ , +ᵤ-id-thick x ω∙)
+-flex (! x) ‵⊤ = just (! ‵⊤ for x , ‵⊤ , subst (‵⊤ ≔_+ ‵⊤) (sym (Unificationₚ.<|-for x)) top)
+-flex (! x) (s ‵+ t) =
  do ! sσ , s' , s+ ← +-flex (! x) s
     ! tσ , t' , t+ ← +-flex (! x) t
     just (! {!!} for x , {!? ‵+ ?!} ‵+ {!!} , {!!})
+-flex (! x) (s ‵× t) = {!!}
+-flex (! x) (# i o t) =
  do i' ← Unification.check x i
     o' ← Unification.check x o
     t' ← Unification.check x t
     just (! (λ {k} → # 0∙ 0∙ t' for x) , # i' o' t' , {!chan!})


+₀-rigidRigid : (x y : Cons multiplicity []) → Maybe (∀ γ → ∃[ r ] _≔_+_ {γ = γ} (con r []) (con x []) (con y []))
+₀-rigidRigid one one = nothing
+₀-rigidRigid zero y = just (λ γ → y , right)
+₀-rigidRigid x zero = just (λ γ → x , left)
+₀-rigidRigid x omega = just (λ γ → omega , shared)
+₀-rigidRigid omega y = just (λ γ → omega , shared)

+₀-amgu : (s t : Usage γ) → Maybe ∃[ σ <| Σ[ r ∈ Usage _ ] r ≔ (σ <| s) + (σ <| t) ]
+₀-amgu {γ = γ} (con x []) (con y []) =
  do f ← +₀-rigidRigid x y
     let foo = f γ
     let (r , sp) = foo
     just (! var , con r [] , sp)
+₀-amgu (var x) t = +-flex x t
+₀-amgu s (var y) =
  do (! σ , r , sp) ← +-flex y s
     just (! σ , r , +-comm sp)

+₁-id-thick : (x : γ ∋= type ▹ δ) (t : δ ⊢= type) → t ≔ (t for x <| var (! x)) + t
+₁-id-thick x t
  with refl , eq ← Unificationₚ.thick-nothing x
  rewrite eq
  = {!!}

-- TODO:
--   - defunctionalise substitutions, a la Subst
--   - use an accumulator?

+₁-amgu : (s t : Type γ) → Maybe ∃[ σ <| ∃[ r ] r ≔ (σ <| s) + (σ <| t) ]
+₁-amgu (var x) t = {!!}
+₁-amgu s (var y) = {!!}
+₁-amgu ‵⊤ ‵⊤ = just {!!}
+₁-amgu (# ix ox tx) (# iy oy ty) =
  do ! iσ , i , isound ← +₀-amgu ix iy
     ! oσ , o , osound ← +₀-amgu (iσ <| ox) (iσ <| oy)
     ! tσ , tsound ← Unificationₚ.unify-sound ((oσ <> iσ) <| tx) ((oσ <> iσ) <| ty)
     let tsound' = trans (sym (Unificationₚ.<|-assoc (sub tσ) (oσ <> iσ) tx))
                         (trans tsound (Unificationₚ.<|-assoc (sub tσ) (oσ <> iσ) ty))
     just (_ , (sub tσ <> (oσ <> iσ))
          , # ((sub tσ <> oσ) <| i) (sub tσ <| o) ((sub tσ <> (oσ <> iσ)) <| tx)
          , subst (λ ● → _ ≔ _ + # _ _ ●) tsound' (chan {!subst !} {!osound!}))
+₁-amgu (lx ‵× rx) (ly ‵× ry) = {!!}
+₁-amgu (lx ‵+ rx) (ly ‵+ ry) = {!!}
+₁-amgu (con {ks = kx} x xs) (con {ks = ky} y ys) with Listₚ.≡-dec decEqKind kx ky
... | no _ = nothing
... | yes refl with decEqCons x y
...           | no _ = nothing
...           | yes refl = {!!}
