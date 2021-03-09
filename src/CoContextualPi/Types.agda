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

import CoContextualPi.StrictUnification
module Unification = CoContextualPi.StrictUnification Kind decEqKind Cons decEqCons
open Unification public
import CoContextualPi.StrictUnification.Properties
module Unificationₚ = CoContextualPi.StrictUnification.Properties Kind decEqKind Cons decEqCons

Usage : KindCtx → Set
Usage γ = γ ⊢= multiplicity

Type : KindCtx → Set
Type γ = γ ⊢= type

infixr 25 #
pattern ‵⊤ = Unification.con top []
pattern # i o t = Unification.con chan (i ∷ o ∷ t ∷ [])
pattern _‵×_ t s = Unification.con prod (t ∷ s ∷ [])
pattern _‵+_ t s = Unification.con sum (t ∷ s ∷ [])
pattern 0∙ = Unification.con zero []
pattern 1∙ = Unification.con one []
pattern ω∙ = Unification.con omega []

private
  variable
    γ : KindCtx
    x y iz ix iy oz ox oy : Usage γ
    a b c t lz lx ly rz rx ry : Type γ

data _≔_+_ {γ} : ∀ {k} → γ ⊢= k → γ ⊢= k → γ ⊢= k → Set where
  -- NOTE: x ≔ y + z is not necessarily unique
  left   : x  ≔ x  + 0∙
  right  : x  ≔ 0∙ + x
  shared : ω∙ ≔ x  + y
  -- NOTE: variables only for types
  var   : ∀ {x y z : γ ∋= type} → var x ≔ var y + var z
  top    : ‵⊤ ≔ ‵⊤ + ‵⊤
  chan   : iz ≔ ix + iy → oz ≔ ox + oy
         → # iz oz t ≔ # ix ox t + # iy oy t
  prod   : lz ≔ lx + ly → rz ≔ rx + ry
         → (lz ‵× rz) ≔ (lx ‵× rx) + (ly ‵× ry)
  sum    : lz ≔ lx + ly → rz ≔ rx + ry
         → (lz ‵+ rz) ≔ (lx ‵+ rx) + (ly ‵+ ry)

+-un : γ ⊢= k → Set
+-un t = t ≔ t + t

Ctx : ℕ → KindCtx → Set
Ctx n γ = Vec (Type γ) n

private
  variable
    A B C : Ctx n γ

data _≔_⊎_ {γ} : Ctx n γ → Ctx n γ → Ctx n γ → Set where
  [] : [] ≔ [] ⊎ []
  _∷_ : (a ≔ b + c) → A ≔ B ⊎ C → (a ∷ A) ≔ (b ∷ B) ⊎ (c ∷ C)

⊎-un : Ctx n γ → Set
⊎-un Γ = Γ ≔ Γ ⊎ Γ
