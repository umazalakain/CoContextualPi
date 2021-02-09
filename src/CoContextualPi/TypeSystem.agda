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

data Term : ℕ → Set where
  top  : Term n
  var  : Fin n  → Term n
  fst  : Term n → Term n
  snd  : Term n → Term n
  inl  : Term n → Term n
  inr  : Term n → Term n
  _‵,_ : Term n → Term n → Term n

data Process : ℕ → Set where
  end  : Process n
  new  : Process (suc n) → Process n
  comp : Process n → Process n → Process n
  recv : Term n → Process (suc n) → Process n
  send : Term n → Term n → Process n → Process n
  case : Term n → Process (suc n) → Process (suc n) → Process n

Ctx : ℕ → ℕ → Set
Ctx n m = Vec (Type m) n

private
  variable
    Γ : Ctx n l
    P Q : Process n
    e f : Term n
    t s : Type l
    x y : Fin n

_∋_∶_ : Ctx n m → Fin n → Type m → Set
Γ ∋ x ∶ t = Vec.lookup Γ x ≡ t

data _⊢_∶_ : Ctx n m → Term n → Type m → Set where
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


data _⊢_ : Ctx n m → Process n → Set where
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

{-
instantiate : Type m → Type zero
instantiate = (λ _ → top) <|_


instantiate-∋ : (Γ : Ctx n m) → Γ ∋ x ∶ t → Vec.map instantiate Γ ∋ x ∶ (instantiate t)
instantiate-∋ Γ refl = Vecₚ.lookup-map _ instantiate Γ


instantiate-⊢ : {Γ : Ctx n m} → Γ ⊢ P → Vec.map instantiate Γ ⊢ P
instantiate-⊢ end = end
instantiate-⊢ (new t p) = new (instantiate t) (instantiate-⊢ p)
instantiate-⊢ (comp p q) = comp (instantiate-⊢ p) (instantiate-⊢ q)
instantiate-⊢ {Γ = Γ} (recv x p) = recv (instantiate-∋ Γ x) (instantiate-⊢ p)
instantiate-⊢ {Γ = Γ} (send x y p) = send (instantiate-∋ Γ x) (instantiate-∋ Γ y) (instantiate-⊢ p)
-}
