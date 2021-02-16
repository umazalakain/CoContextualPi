open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Function using (_∘_)

open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Product as Product using (_,_)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)


module CoContextualPi.Types where

private
  variable
    n m l : ℕ


data Kind : Set where
  type multiplicity : Kind

decEqKind : (x y : Kind) → Dec (x ≡ y)
decEqKind type type = yes refl
decEqKind type multiplicity = no (λ ())
decEqKind multiplicity type = no (λ ())
decEqKind multiplicity multiplicity = yes refl

data Cons : Kind → List Kind → Set where
  top            : Cons type []
  chan           : Cons type (multiplicity ∷ multiplicity ∷ type ∷ [])
  prod sum       : Cons type (type ∷ type ∷ [])
  zero one omega : Cons multiplicity []

private
  variable
    k : Kind
    ks : List Kind

decEqCons : (x y : Cons k ks) → Dec (x ≡ y)
decEqCons top top = yes refl
decEqCons chan chan = yes refl
decEqCons prod prod = yes refl
decEqCons prod sum = no (λ ())
decEqCons sum prod = no (λ ())
decEqCons sum sum = yes refl
decEqCons zero zero = yes refl
decEqCons zero one = no (λ ())
decEqCons zero omega = no (λ ())
decEqCons one zero = no (λ ())
decEqCons one one = yes refl
decEqCons one omega = no (λ ())
decEqCons omega zero = no (λ ())
decEqCons omega one = no (λ ())
decEqCons omega omega = yes refl

open import CoContextualPi.StrictUnification Kind decEqKind Cons decEqCons as Unification
  using (KindCtx; Univ; _⊢_; _⊢'_)
open import CoContextualPi.StrictUnification.Properties Kind decEqKind Cons decEqCons
  using (unify-sound) public


Multiplicity : KindCtx → Set
Multiplicity γ = γ ⊢ multiplicity

Type : KindCtx → Set
Type γ = γ ⊢ type

infixr 25 #
pattern ‵⊤ = Unification.con top []
pattern # i o t = Unification.con chan (i ∷ o ∷ t ∷ [])
pattern _‵×_ t s = Unification.con prod (t ∷ s ∷ [])
pattern _‵+_ t s = Unification.con sum (t ∷ s ∷ [])
pattern 0∙ = Unification.con zero []
pattern 1∙ = Unification.con one []
pattern ω∙ = Unification.con omega []

{-
private
  variable
    u : Univ
    x y : Usage
    a b c t lz lx ly rz rx ry : Type m

-- x ≔ y + z is not necessarily unique
data _≔_+₀_ : Usage → Usage → Usage → Set where
  0-left  : y  ≔ 0∙ +₀ y
  0-right : x  ≔ x  +₀ 0∙
  ω-right : ω∙ ≔ x  +₀ ω∙
  ω-left  : ω∙ ≔ ω∙ +₀ y
  1-both  : ω∙ ≔ 1∙ +₀ 1∙

data _≔_+₁_ {m} : Type m → Type m → Type m → Set where
  var   : ∀ {x y z} → var x ≔ var y +₁ var z
  top   : ‵⊤ ≔ ‵⊤ +₁ ‵⊤
  chan  : iz ≔ ix +₀ iy → oz ≔ ox +₀ oy
        → # iz oz t ≔ # ix ox t +₁ # iy oy t
  prod  : lz ≔ lx +₁ ly → rz ≔ rx +₁ ry
        → (lz ‵× rz) ≔ (lx ‵× rx) +₁ (ly ‵× ry)
  sum   : lz ≔ lx +₁ ly → rz ≔ rx +₁ ry
        → (lz ‵+ rz) ≔ (lx ‵+ rx) +₁ (ly ‵+ ry)

un₁ : Type m → Set
un₁ t = t ≔ t +₁ t

Ctx : ℕ → ℕ → Set
Ctx n m = Vec (Type m) n

private
  variable
    A B C : Ctx n m

data _≔_+₂_ {m} : Ctx n m → Ctx n m → Ctx n m → Set where
  [] : [] ≔ [] +₂ []
  _∷_ : (a ≔ b +₁ c) → A ≔ B +₂ C → (a ∷ A) ≔ (b ∷ B) +₂ (c ∷ C)

un₂ : Ctx n m → Set
un₂ Γ = Γ ≔ Γ +₂ Γ
-}
