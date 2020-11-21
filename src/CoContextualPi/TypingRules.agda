
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)

open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product as Product using (Σ; _×_; ∃-syntax; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Vec as Vec using (Vec; []; _∷_)

import Data.Vec.Properties as Vecₚ

open import CoContextualPi.Types

module CoContextualPi.TypingRules where


private
  variable
    n m l k : ℕ


data Process : ℕ → Set where
  end  : Process n
  new  : Process (suc n) → Process n
  comp : Process n → Process n → Process n
  recv : Fin n → Process (suc n) → Process n
  send : Fin n → Fin n → Process n → Process n


Ctx : ℕ → ℕ → Set
Ctx n m = Vec (Type m) n


private
  variable
    Γ : Ctx n l
    P Q : Process n
    t : Type l
    x y : Fin n


_∋_∶_ : Ctx n m → Fin n → Type m → Set
Γ ∋ x ∶ t = Vec.lookup Γ x ≡ t


data _⊢_ : Ctx n m → Process n → Set where
  end : Γ ⊢ end

  new : (t : Type m)
      → (t ∷ Γ) ⊢ P
      → Γ ⊢ new P

  comp : Γ ⊢ P
       → Γ ⊢ Q
       → Γ ⊢ (comp P Q)

  recv : Γ ∋ x ∶ # t
       → (t ∷ Γ) ⊢ P
       → Γ ⊢ recv x P

  send : Γ ∋ x ∶ # t
       → Γ ∋ y ∶ t
       → Γ ⊢ P
       → Γ ⊢ send x y P


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
