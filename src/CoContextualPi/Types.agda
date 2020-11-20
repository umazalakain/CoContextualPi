open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin; zero; suc)


module CoContextualPi.Types where

private
  variable
    n m l : ℕ


infixr 40 ′_
infix 30 _↦_ _for_
infixr 25 #_
infix 15 _<>_
infix 10 _≗_


data Type (n : ℕ) : Set where
  ′_    : Fin n → Type n
  top   : Type n
  #_    : Type n → Type n
  <_,_> : Type n → Type n → Type n


-- Renaming
|> : (Fin n → Fin m) → Fin n → Type m
|> f = ′_ ∘ f


-- Substitution
_<|_ : (Fin n → Type m) → Type n → Type m
f <| (′ x) = f x
f <| top = top
f <| (# t) = # (f <| t)
f <| < t₁ , t₂ > = < f <| t₁ , f <| t₂ >


-- Extensional equality of substitutions
_≗_ : (Fin n → Type m) → (Fin n → Type m) → Set
f ≗ g = ∀ x → f x ≡ g x


-- Composition of substitutions
_<>_ : (Fin m → Type n) → (Fin l → Type m) → (Fin l → Type n)
f <> g = f <|_ ∘ g


-- A renaming (thin x) pushes up everithing x and above
thin : Fin (suc n) → Fin n → Fin (suc n)
thin zero y = suc y
thin (suc x) zero = zero
thin (suc x) (suc y) = suc (thin x y)


-- A renaming (thick x) tries to lower everything above x
-- Only succeeds if x itself is not present
thick : Fin (suc n) → Fin (suc n) → Maybe (Fin n)
thick zero zero = nothing
thick zero (suc y) = just y
thick {suc n} (suc x) zero = just zero
thick {suc n} (suc x) (suc y) = Maybe.map suc (thick x y)


-- The substitution (t for x) y results in t if x ≡ y and in y otherwise
_for_ : Type n → Fin (suc n) → Fin (suc n) → Type n
(t for x) y = Maybe.maybe ′_ t (thick x y)


-- Defunctionalise substitutions
data Subst (n : ℕ) : Set where
  _↦_ : Fin (suc n) → Type n → Subst n


-- Sequences of substitutions, each gets rid of one variable
-- The sequence AList m n starts with m variables and ends with n
data AList : ℕ → ℕ → Set where
  [] : ∀ {n} → AList n n
  _-,_ : ∀ {m n} → AList m n → Subst m → AList (suc m) n


_++_ : AList m n → AList l m → AList l n
xs ++ [] = xs
xs ++ (ys -, x) = (xs ++ ys) -, x


sub : AList m n → Fin m → Type n
sub [] = ′_
sub (σs -, x ↦ t) = sub σs <> (t for x)
