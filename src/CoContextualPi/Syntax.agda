open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.List.Base using (List)
open import Relation.Nullary using (Dec)

module CoContextualPi.Syntax where

record Syntax : Set₁ where
  field
    Kind : Set
    Con : Kind → List Kind → Set
    decEqKind : (x y : Kind) → Dec (x ≡ y)
    decEqCon : ∀ {k} {ks} → (x y : Con k ks) → Dec (x ≡ y)
