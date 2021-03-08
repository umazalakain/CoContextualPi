open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; trans; cong; sym )
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
open Unification using (|>; _<|_; Subst; var; con; zero; suc; sub; !_; []; _∋_; _∋_▹_; _for_; _<>_)
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
    x y z : Usage γ
    t s r : Type γ
    Γ Δ Θ : Ctx n γ

+₀-<| : (σ : ∀ {k} → γ ∋ k → δ Unification.⊢ k) → x ≔ y +₀ z → (σ <| x) ≔ (σ <| y) +₀ (σ <| z)
+₀-<| σ left = left
+₀-<| σ right = right
+₀-<| σ shared = shared

FSubst : ∀ {p} {γ : KindCtx} → ({δ : KindCtx} → (∀ {k} → γ ∋ k → δ Unification.⊢ k) → Set p) → Set p
FSubst {γ = γ} P = ∃[ δ ] (Σ[ σ ∈ (∀ {k} → γ ∋ k → δ Unification.⊢ k) ] P σ)
syntax FSubst (λ σ → A) = ∃[ σ <| A ]


+₀-comm : x ≔ y +₀ z → x ≔ z +₀ y
+₀-comm left = right
+₀-comm right = left
+₀-comm shared = shared

+₀-id-thick : (x : γ ∋ multiplicity ▹ δ) (t : δ Unification.⊢ multiplicity) → t ≔ (0∙ for x <| var (! x)) +₀ t
+₀-id-thick x t
  with refl , eq ← Unificationₚ.thick-nothing x
  rewrite eq = right

+₀-flex : (x : γ ∋ multiplicity) (t : γ Unification.⊢ multiplicity) → Maybe ∃[ σ <| ∃[ r ] r ≔ (σ <| var x) +₀ (σ <| t) ]
+₀-flex (! x) (var y) = just (! 0∙ for x , (0∙ for x) y , +₀-id-thick x ((0∙ for x) y))
+₀-flex (! x) 0∙ = just (! 0∙ for x , 0∙ , +₀-id-thick x 0∙)
+₀-flex (! x) 1∙ = just (! 0∙ for x , 1∙ , +₀-id-thick x 1∙)
+₀-flex (! x) ω∙ = just (! 0∙ for x , ω∙ , +₀-id-thick x ω∙)

+₀-rigidRigid : (x y : Cons multiplicity []) → Maybe (∀ γ → ∃[ r ] _≔_+₀_ {γ = γ} (con r []) (con x []) (con y []))
+₀-rigidRigid one one = nothing
+₀-rigidRigid zero y = just (λ γ → y , right)
+₀-rigidRigid x zero = just (λ γ → x , left)
+₀-rigidRigid x omega = just (λ γ → omega , shared)
+₀-rigidRigid omega y = just (λ γ → omega , shared)

+₀-amgu : (s t : Usage γ) → Maybe ∃[ σ <| Σ[ r ∈ Usage _ ] r ≔ (σ <| s) +₀ (σ <| t) ]
+₀-amgu {γ = γ} (con x []) (con y []) =
  do f ← +₀-rigidRigid x y
     let foo = f γ
     let (r , sp) = foo
     just (! var , con r [] , sp)
+₀-amgu (var x) t = +₀-flex x t
+₀-amgu s (var y) =
  do (! σ , r , sp) ← +₀-flex y s
     just (! σ , r , +₀-comm sp)

+₁-id-thick : (x : γ ∋ type ▹ δ) (t : δ Unification.⊢ type) → t ≔ ({!!} for x <| var (! x)) +₁ t
+₁-id-thick x t
  with refl , eq ← Unificationₚ.thick-nothing x
  = {!!}

+₁-flex : (x : γ ∋ type) (t : γ Unification.⊢ type) → Maybe ∃[ σ <| Σ[ r ∈ Type _ ] r ≔ (σ <| var x) +₁ (σ <| t) ]
+₁-flex (! x) (var y) = just (! |> (Product.map _ suc) , var (! zero) , var )
+₁-flex (! x) ‵⊤ = just (! ‵⊤ for x , ‵⊤ , {!!})
+₁-flex (! x) (s ‵+ t) = {!!}
+₁-flex (! x) (s ‵× t) = {!!}
+₁-flex (! x) (# i o t) =
  do i' ← Unification.check x i
     o' ← Unification.check x o
     t' ← Unification.check x t
     just (! (λ {k} → # 0∙ 0∙ t' for x) , # i' o' t' , {!chan!})

+₁-amgu : (s t : Type γ) → Maybe ∃[ σ <| ∃[ r ] r ≔ (σ <| s) +₁ (σ <| t) ]
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
          , subst (λ ● → _ ≔ _ +₁ # _ _ ●) tsound' (chan {!subst !} {!osound!}))
+₁-amgu (lx ‵× rx) (ly ‵× ry) = {!!}
+₁-amgu (lx ‵+ rx) (ly ‵+ ry) = {!!}
+₁-amgu (con {ks = kx} x xs) (con {ks = ky} y ys) with Listₚ.≡-dec decEqKind kx ky
... | no _ = nothing
... | yes refl with decEqCons x y
...           | no _ = nothing
...           | yes refl = {!!}
