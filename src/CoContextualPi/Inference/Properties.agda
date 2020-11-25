
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; trans; inspect) renaming ([_] to I[_])

open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product as Product using (Σ; _×_; ∃-syntax; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Vec as Vec using (Vec; []; _∷_; [_])

import Data.Vec.Properties as Vecₚ

open import CoContextualPi.Types
open import CoContextualPi.TypingRules
open import CoContextualPi.Unification
open import CoContextualPi.Unification.Properties
open import CoContextualPi.Inference

module CoContextualPi.Inference.Properties where

private
  variable
    n m l k : ℕ
    P Q : Process n


[_]⇓-∋ : (σ : Fin m → Type l) (xs : Ctx n m) {x : Fin n} {t : Type m}
       → xs ∋ x ∶ t
       → [ σ ]⇓ xs ∋ x ∶ (σ <| t)
[ σ ]⇓-∋ (_ ∷ _) {zero} refl = refl
[ σ ]⇓-∋ (_ ∷ xs) {suc x} refl = Vecₚ.lookup-map _ _ xs


[_]⇓-⊢ : (σ : Fin m → Type l) {xs : Ctx n m} {P : Process n} → xs ⊢ P → [ σ ]⇓ xs ⊢ P
[ σ ]⇓-⊢ end = end
[ σ ]⇓-⊢ (new t ⊢P) = new _ ([ σ ]⇓-⊢ ⊢P)
[ σ ]⇓-⊢ (comp ⊢P ⊢Q) = comp ([ σ ]⇓-⊢ ⊢P) ([ σ ]⇓-⊢ ⊢Q)
[ σ ]⇓-⊢ {xs} (recv x ⊢P) = recv ([ σ ]⇓-∋ xs x) ([ σ ]⇓-⊢ ⊢P)
[ σ ]⇓-⊢ {xs} (send x y ⊢P) = send ([ σ ]⇓-∋ xs x) ([ σ ]⇓-∋ xs y) ([ σ ]⇓-⊢ ⊢P)


unify-⊢ : {xs : Ctx n m} {ys : Ctx n l} (lhs rhs : Vec (Type m) k) {P : Process n} → xs ⊢ P
        → unify-apply lhs rhs xs ≡ just (l , ys)
        → ys ⊢ P
unify-⊢ lhs rhs ⊢P eq with unify lhs rhs
unify-⊢ lhs rhs ⊢P refl | just (_ , σ) = [ sub σ ]⇓-⊢ ⊢P


merge-⊢ : (xs : Ctx n l) (ys : Ctx n m) {zs : Ctx n k}
        → unify-apply ([ |> left-inject ]⇓ xs) ([ |> right-inject ]⇓ ys) ([ |> left-inject ]⇓ xs) ≡ just (k , zs)
        → unify-apply ([ |> left-inject ]⇓ xs) ([ |> right-inject ]⇓ ys) ([ |> right-inject ]⇓ ys) ≡ just (k , zs)
merge-⊢ xs ys eq
  with just σ ← unify ([ |> left-inject ]⇓ xs) ([ |> right-inject ]⇓ ys)
     | I[ req ] ← inspect (unify ([ |> left-inject ]⇓ xs)) ([ |> right-inject ]⇓ ys)
  rewrite unify-sound ([ |> left-inject ]⇓ xs) ([ |> right-inject ]⇓ ys) req
  = eq

infer-sound-comp : {xs : Ctx n l} {ys : Ctx n m} {zs : Ctx n k} {P Q : Process n}
                → xs ⊢ P → ys ⊢ Q
                → merge xs ys ≡ just (k , zs)
                → zs ⊢ comp P Q
infer-sound-comp {xs = xs} {ys = ys} ⊢P ⊢Q eq
  = comp (unify-⊢ ([ |> left-inject ]⇓ xs) ([ |> right-inject ]⇓ ys) ([ |> left-inject ]⇓-⊢ ⊢P) eq)
         (unify-⊢ ([ |> left-inject ]⇓ xs) ([ |> right-inject ]⇓ ys) ([ |> right-inject ]⇓-⊢ ⊢Q) (merge-⊢ xs ys eq))


infer-sound-recv : (x : Fin n) {y : Type m} {Γ : Ctx n m} {Γ' : Ctx n l}
                → (y ∷ Γ) ⊢ P
                → unify-apply [ Vec.lookup Γ x ] [ # y ] Γ ≡ just (l , Γ')
                → Γ' ⊢ recv x P
infer-sound-recv x {y} {Γ} ⊢P eq
  with just (_ , σ) ← amgu (Vec.lookup Γ x) (# y) []
     | I[ req ]     ← inspect (amgu (Vec.lookup Γ x) (# y)) []
  with refl ← eq
  = recv (trans (Vecₚ.lookup-map _ _ Γ) (amgu-sound (Vec.lookup Γ x) _ _ _ req))
         ([ sub σ ]⇓-⊢ ⊢P)

infer-sound-send : (x y : Fin n) {Γ : Ctx n m} {Γ' : Ctx n l}
                → Γ ⊢ P
                → unify-apply [ Vec.lookup Γ x ] [ # Vec.lookup Γ y ] Γ ≡ just (l , Γ')
                → Γ' ⊢ send x y P
infer-sound-send x y {Γ} ⊢P eq
  with just (_ , σ) ← amgu (Vec.lookup Γ x) (# Vec.lookup Γ y) []
     | I[ req ]     ← inspect (amgu (Vec.lookup Γ x) (# Vec.lookup Γ y)) []
  with refl ← eq
  = send (trans (Vecₚ.lookup-map _ _ Γ) (amgu-sound (Vec.lookup Γ x) _ _ _ req))
         (Vecₚ.lookup-map _ _ Γ)
         ([ sub σ ]⇓-⊢ ⊢P)


infer-sound : (P : Process n) {Γ : Ctx n l} → infer P ≡ just (l , Γ) → Γ ⊢ P
infer-sound end eq = end
infer-sound (new P) eq with infer P | inspect infer P
infer-sound (new P) refl | just (_ , t ∷ Γ) | I[ eq ] = new t (infer-sound P eq)
infer-sound (comp P Q) eq with infer P | inspect infer P
infer-sound (comp P Q) eq | just (_ , ΓP) | I[ peq ] with infer Q | inspect infer Q
infer-sound (comp P Q) eq | just (_ , ΓP) | I[ peq ] | just (_ , ΓQ) | I[ qeq ] = infer-sound-comp (infer-sound P peq) (infer-sound Q qeq) eq
infer-sound (recv x P) eq with infer P | inspect infer P
infer-sound (recv x P) eq | just (_ , y ∷ Γ) | I[ qe ] = infer-sound-recv x (infer-sound P qe) eq
infer-sound (send x y P) eq with infer P | inspect infer P
infer-sound (send x y P) eq | just Γ | I[ qe ] = infer-sound-send x y (infer-sound P qe) eq
