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
open Unification using (KindCtx) public
import CoContextualPi.StrictUnification.Properties
module Unificationₚ = CoContextualPi.StrictUnification.Properties Kind decEqKind Cons decEqCons

Usage : KindCtx → Set
Usage γ = γ Unification.⊢ multiplicity

Type : KindCtx → Set
Type γ = γ Unification.⊢ type

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

-- x ≔ y + z is not necessarily unique
data _≔_+₀_ {γ} : Usage γ → Usage γ → Usage γ → Set where
  var     : ∀ {x y z} → Unification.var x ≔ Unification.var y +₀ Unification.var z
  erased  : 0∙ ≔ 0∙ +₀ 0∙
  1-left  : 1∙ ≔ 1∙ +₀ 0∙
  1-right : 1∙ ≔ 0∙ +₀ 1∙
  shared  : ω∙ ≔ x  +₀ y

data _≔_+₁_ {γ} : Type γ → Type γ → Type γ → Set where
  var   : ∀ {x y z} → Unification.var x ≔ Unification.var y +₁ Unification.var z
  top   : ‵⊤ ≔ ‵⊤ +₁ ‵⊤
  chan  : iz ≔ ix +₀ iy → oz ≔ ox +₀ oy
        → # iz oz t ≔ # ix ox t +₁ # iy oy t
  prod  : lz ≔ lx +₁ ly → rz ≔ rx +₁ ry
        → (lz ‵× rz) ≔ (lx ‵× rx) +₁ (ly ‵× ry)
  sum   : lz ≔ lx +₁ ly → rz ≔ rx +₁ ry
        → (lz ‵+ rz) ≔ (lx ‵+ rx) +₁ (ly ‵+ ry)

un₁ : Type γ → Set
un₁ t = t ≔ t +₁ t

Ctx : ℕ → KindCtx → Set
Ctx n γ = Vec (Type γ) n

private
  variable
    A B C : Ctx n γ

data _≔_+₂_ {γ} : Ctx n γ → Ctx n γ → Ctx n γ → Set where
  [] : [] ≔ [] +₂ []
  _∷_ : (a ≔ b +₁ c) → A ≔ B +₂ C → (a ∷ A) ≔ (b ∷ B) +₂ (c ∷ C)

un₂ : Ctx n γ → Set
un₂ Γ = Γ ≔ Γ +₂ Γ
