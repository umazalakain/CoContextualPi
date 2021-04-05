open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; _≢_)

open import Data.Product as Product using (Σ; _×_; ∃-syntax; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Vec as Vec using (Vec; []; _∷_)

open import CoContextualPi.Types

module CoContextualPi.TypeSystem where

private
  variable
    n m l k : ℕ

data Expr : ℕ → Set where
  top  : Expr n
  var  : Fin n  → Expr n
  fst  : Expr n → Expr n
  snd  : Expr n → Expr n
  inl  : Expr n → Expr n
  inr  : Expr n → Expr n
  _‵,_ : Expr n → Expr n → Expr n

data Proc : ℕ → Set where
  end  : Proc n
  new  : Proc (suc n) → Proc n
  comp : Proc n → Proc n → Proc n
  recv : Expr n → Proc (suc n) → Proc n
  send : Expr n → Expr n → Proc n → Proc n
  case : Expr n → Proc (suc n) → Proc (suc n) → Proc n


private
  variable
    γ : KindCtx
    Γ Δ Ξ Ω Ψ : Ctx n γ
    P Q : Proc n
    e f : Expr n
    t s : Type γ
    x y : Fin n

data _∋_∶_▹_ : Ctx n γ → Fin n → Type γ → Ctx m γ → Set where
  zero : (t ∷ Γ) ∋ x ∶ t ▹ Γ
  suc  : Γ ∋ x ∶ t ▹ Δ → (s ∷ Γ) ∋ suc x ∶ t ▹ (s ∷ Δ)

_∋_∶_ : Ctx n γ → Fin n → Type γ → Set
_∋_∶_ {n = suc n} Γ x t = Σ[ Δ ∈ Ctx n _ ] Γ ∋ x ∶ t ▹ Δ × ⊎-un Δ

data _⊢_∶_ : Ctx n γ → Expr n → Type γ → Set where
  top : ⊎-un Γ
      → Γ ⊢ top ∶ ‵⊤

  var : Γ ∋ x ∶ t
      → Γ ⊢ var x ∶ t

  fst : +-un s
      → Γ ⊢ e ∶ (t ‵× s)
      → Γ ⊢ fst e ∶ t

  snd : +-un t
      → Γ ⊢ e ∶ (t ‵× s)
      → Γ ⊢ snd e ∶ s

  inl : Γ ⊢ e ∶ t
      → Γ ⊢ inl e ∶ (t ‵+ s)

  inr : Γ ⊢ e ∶ s
      → Γ ⊢ inr e ∶ (t ‵+ s)

  pair : Γ ≔ Δ ⊎ Ξ
       → Δ ⊢ e ∶ s
       → Ξ ⊢ f ∶ t
       → Γ ⊢ (e ‵, f) ∶ (s ‵× t)


data _⊢_ : Ctx n γ → Proc n → Set where
  end : ⊎-un Γ
      → Γ ⊢ end

  new : (t : Type γ)
      → (t ∷ Γ) ⊢ P
      → Γ ⊢ new P

  comp : Γ ≔ Δ ⊎ Ξ
       → Δ ⊢ P
       → Ξ ⊢ Q
       → Γ ⊢ comp P Q

  recv : Γ ≔ Δ ⊎ Ξ
       → Δ ⊢ e ∶ # 1∙ 0∙ t
       → (t ∷ Ξ) ⊢ P
       → Γ ⊢ recv e P

  send : Γ ≔ Δ ⊎ Ξ
       → Ξ ≔ Ω ⊎ Ψ
       → Δ ⊢ e ∶ # 0∙ 1∙ t
       → Ω ⊢ f ∶ t
       → Ψ ⊢ P
       → Γ ⊢ send e f P

  case : Γ ≔ Δ ⊎ Ξ
       → Δ ⊢ e ∶ (t ‵+ s)
       → (t ∷ Ξ) ⊢ P
       → (s ∷ Ξ) ⊢ Q
       → Γ ⊢ (case e P Q)
