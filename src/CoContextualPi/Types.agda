open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)


module CoContextualPi.Types where

private
  variable
    n m l k : ℕ


data Cons : ℕ → Set where
  Top  : Cons 0
  Chan : Cons 1
  Prod : Cons 2
  Sum  : Cons 2

Cons-dec : (x y : Cons k) → Dec (x ≡ y)
Cons-dec Top Top = yes refl
Cons-dec Chan Chan = yes refl
Cons-dec Prod Prod = yes refl
Cons-dec Prod Sum = no λ ()
Cons-dec Sum Prod = no λ ()
Cons-dec Sum Sum = yes refl

open import CoContextualPi.Unification Cons Cons-dec as Unification
  renaming (Term to Type; UTerm to UType) public


infixr 25 #_
pattern #_ t = Unification.con Chan (t ∷ [])
pattern _‵×_ t s = Unification.con Prod (t ∷ s ∷ [])
pattern _‵+_ t s = Unification.con Sum (t ∷ s ∷ [])
