open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Category.Functor
open import Category.Monad
open import Category.Applicative

import Data.Maybe.Categorical as maybeCat
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Product as Product using (∃; Σ-syntax; _,_)
open import Data.Maybe as Maybe using (Maybe; just; nothing)

open import CoContextualPi.Types
open Unification using (|>; _<|_; Subst; var; con; zero; suc; sub; !_; []; _∋_; _for_)
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
    γ δ : KindCtx
    x y z : Usage γ
    t s r : Type γ
    Γ Δ Θ : Ctx n γ

uamgu : (s t : Usage γ) → Maybe (Σ[ δ ∈ KindCtx ] Σ[ σ ∈ (∀ {k} → γ ∋ k  → δ Unification.⊢ k) ] Σ[ r ∈ Usage δ ] r ≔ (σ <| s) +₀ (σ <| t))
uamgu (var x) (var y) = just (_ , |> (Product.map _ suc) , var (! zero) , var)
uamgu (var (! x)) 0∙ 
  with _ , eq ← Unificationₚ.thick-nothing x
  rewrite eq
  = just (_ , 0∙ for x , 0∙ , {!!})
uamgu (var x) 1∙ = {!!}
uamgu (var x) ω∙ = {!!}
uamgu (con x x₁) t = {!!}

tamgu : (s t : Type γ) → Maybe (Σ[ δ ∈ KindCtx ] Σ[ σ ∈ (∀ {k} → γ ∋ k  → δ Unification.⊢ k) ] Σ[ r ∈ Type δ ] r ≔ (σ <| s) +₁ (σ <| t))
tamgu (var x) (var x₁) = just (_ , |> (Product.map _ suc) , var (! zero) , var)
tamgu (var (! x)) ‵⊤ = just (_ , ‵⊤ for x , ‵⊤ , {!!})
tamgu (var x) (# i o t) = {!!}
tamgu (var x) (s ‵× t) = {!!}
tamgu (var x) (s ‵+ t) = {!!}
tamgu (con x x₁) (var y) = {!!}
tamgu ‵⊤ ‵⊤ = just {!!}
tamgu (# ix ox tx) (# iy oy ty) = do ! iσ , i , isound ← uamgu ix iy
                                     ! oσ , o , osound ← uamgu ox oy -- FIXME: this should take iσ as input
                                     ! tσ ← Unification.amgu refl tx ty {!oσ!}
                                     {!!}
tamgu (lx ‵× rx) (ly ‵× ry) = {!!}
tamgu (lx ‵+ rx) (ly ‵+ ry) = {!!}
tamgu x y = {!!}
