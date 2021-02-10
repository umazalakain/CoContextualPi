open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)

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

Ctx : ℕ → ℕ → Set
Ctx n m = Vec (Type m) n

private
  variable
    Γ : Ctx n l
    P Q : Proc n
    e f : Expr n
    t s : Type l
    x y : Fin n

_∋_∶_ : Ctx n m → Fin n → Type m → Set
Γ ∋ x ∶ t = Vec.lookup Γ x ≡ t

data _⊢_∶_ : Ctx n m → Expr n → Type m → Set where
  top : Γ ⊢ top ∶ ‵⊤

  var : Γ ∋ x ∶ t
      → Γ ⊢ var x ∶ t

  fst : Γ ⊢ e ∶ (t ‵× s)
      → Γ ⊢ fst e ∶ t

  snd : Γ ⊢ e ∶ (t ‵× s)
      → Γ ⊢ snd e ∶ s

  inl : Γ ⊢ e ∶ t
      → Γ ⊢ inl e ∶ (t ‵+ s)

  inr : Γ ⊢ e ∶ s
      → Γ ⊢ inr e ∶ (t ‵+ s)

  _‵,_ : Γ ⊢ e ∶ s
       → Γ ⊢ f ∶ t
       → Γ ⊢ (e ‵, f) ∶ (s ‵× t)


data _⊢_ : Ctx n m → Proc n → Set where
  end : Γ ⊢ end

  new : (t : Type m)
      → (t ∷ Γ) ⊢ P
      → Γ ⊢ new P

  comp : Γ ⊢ P
       → Γ ⊢ Q
       → Γ ⊢ (comp P Q)

  recv : Γ ⊢ e ∶ # t
       → (t ∷ Γ) ⊢ P
       → Γ ⊢ recv e P

  send : Γ ⊢ e ∶ # t
       → Γ ⊢ f ∶ t
       → Γ ⊢ P
       → Γ ⊢ send e f P

  case : Γ ⊢ e ∶ (t ‵+ s)
       → (t ∷ Γ) ⊢ P
       → (s ∷ Γ) ⊢ Q
       → Γ ⊢ (case e P Q)
