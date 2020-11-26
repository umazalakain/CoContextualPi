open import Category.Functor
open import Category.Monad
open import Category.Applicative
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; sym; trans; inspect) renaming ([_] to I[_])

open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product as Product using (Σ; _×_; ∃-syntax; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Vec as Vec using (Vec; []; _∷_; [_])

import Data.Maybe.Categorical as maybeCat
import Data.Vec.Properties as Vecₚ

open import CoContextualPi.Types
open import CoContextualPi.TypeSystem
open import CoContextualPi.Unification.Properties Cons Cons-dec
open import CoContextualPi.Inference

module CoContextualPi.Inference.Properties where

private
  variable
    n m l k : ℕ
    P Q : Process n

private
  -- Help ourselves to some goodies
  open RawFunctor {{...}}
  open RawApplicative {{...}} hiding (_<$>_)
  open RawMonad {{...}} hiding (_<$>_; _⊛_)
  instance maybeFunctor = maybeCat.functor
  instance maybeMonad = maybeCat.monad
  instance maybeApplicative = maybeCat.applicative


<|-lookup : (σ : Fin m → Type l) (xs : Vec (Type m) n) {i : Fin n}
          → Vec.lookup ((σ <|) xs) i ≡ (σ <|) (Vec.lookup xs i)
<|-lookup σ (x ∷ xs) {zero} = refl
<|-lookup σ (x ∷ xs) {suc i} = <|-lookup σ xs

<|-∋ : (σ : Fin m → Type l) (xs : Vec (Type m) n) {x : Fin n} {t : Type m}
     → xs ∋ x ∶ t → ((σ <|) xs) ∋ x ∶ ((σ <|) t)
<|-∋ σ xs refl = <|-lookup σ xs

<|-⊢ : (σ : Fin m → Type l) {xs : Vec (Type m) n} {P : Process n} → xs ⊢ P → ((σ <|) xs) ⊢ P
<|-⊢ σ end = end
<|-⊢ σ (new t ⊢P) = new _ (<|-⊢ σ ⊢P)
<|-⊢ σ (comp ⊢P ⊢Q) = comp (<|-⊢ σ ⊢P) (<|-⊢ σ ⊢Q)
<|-⊢ σ {xs} (recv x ⊢P) = recv (<|-∋ σ xs x) (<|-⊢ σ ⊢P)
<|-⊢ σ {xs} (send x y ⊢P) = send (<|-∋ σ xs x) (<|-∋ σ xs y) (<|-⊢ σ ⊢P)


unify-⊢ : {xs : Vec (Type m) n} {ys : Vec (Type l) n} (lhs rhs : Vec (Type m) k) {P : Process n}
        → xs ⊢ P → unify-apply lhs rhs xs ≡ just (l , ys) → ys ⊢ P
unify-⊢ lhs rhs ⊢P eq with unify lhs rhs
unify-⊢ lhs rhs ⊢P refl | just (_ , σ) = <|-⊢ (sub σ) ⊢P


merge-⊢ : (xs : Ctx n l) (ys : Ctx n m) {zs : Ctx n k}
        → unify-apply ((|> left-inject <|) xs) ((|> right-inject <|) ys) ((|> left-inject <|) xs) ≡ just (k , zs)
        → unify-apply ((|> left-inject <|) xs) ((|> right-inject <|) ys) ((|> right-inject <|) ys) ≡ just (k , zs)
merge-⊢ xs ys eq
  with just σ ← unify ((|> left-inject <|) xs) ((|> right-inject <|) ys)
     | I[ req ] ← inspect (unify ((|> left-inject <|) xs)) ((|> right-inject <|) ys)
  rewrite sym (amgu-sound ((|> left-inject <|) xs) ((|> right-inject <|) ys) idSubst req)
  = eq



infer-sound : (P : Process n) {Γ : Ctx n l} → infer P ≡ just (l , Γ) → Γ ⊢ P

infer-sound end eq = end

infer-sound (new P) eq
  with just (_ , t ∷ Γ) ← infer P | I[ qe ] ← inspect infer P
  with refl ← eq
  = new t (infer-sound P qe)

infer-sound (comp P Q) eq
  with just (_ , ΓP) ← infer P | I[ peq ] ← inspect infer P
  with just (_ , ΓQ) ← infer Q | I[ qeq ] ← inspect infer Q
  = comp (unify-⊢ ((|> left-inject <|) ΓP) _ (<|-⊢ _ (infer-sound P peq)) eq)
         (unify-⊢ ((|> left-inject <|) ΓP) _ (<|-⊢ _ (infer-sound Q qeq)) (merge-⊢ ΓP ΓQ eq))

infer-sound (recv x P) eq
  with just (_ , y ∷ Γ) ← infer P | I[ qe ] ← inspect infer P
  with just (_ , σ) ← unify (Vec.lookup Γ x) (# y)
     | I[ req ]     ← inspect (unify (Vec.lookup Γ x)) (# y)
  with refl ← eq
  = recv (trans (<|-lookup (sub σ) Γ) (unify-sound (Vec.lookup Γ x) _ req))
         (<|-⊢ (sub σ) (infer-sound P qe))

infer-sound (send x y P) eq
  with just (_ , Γ) ← infer P | I[ qe ] ← inspect infer P
  with just (_ , σ) ← unify (Vec.lookup Γ x) (# Vec.lookup Γ y)
     | I[ req ]     ← inspect (unify (Vec.lookup Γ x)) (# Vec.lookup Γ y)
  with refl ← eq
  = send (trans (<|-lookup (sub σ) Γ) (amgu-sound (Vec.lookup Γ x) _ _ req))
         (<|-lookup (sub σ) Γ)
         (<|-⊢ (sub σ) (infer-sound P qe))
