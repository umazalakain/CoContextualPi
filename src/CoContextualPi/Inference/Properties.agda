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
import Data.Maybe.Properties as Maybeₚ
import Data.Nat.Properties as ℕₚ

open import CoContextualPi.Types
open import CoContextualPi.TypeSystem
open import CoContextualPi.Unification.Properties Cons Cons-dec
open import CoContextualPi.Inference

module CoContextualPi.Inference.Properties where

private
  variable
    n m l k : ℕ
    P Q : Proc n

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

<|-⊢-∶ : (σ : Fin m → Type l) {xs : Vec (Type m) n} {e : Expr n} {t : Type m}
       → xs ⊢ e ∶ t → ((σ <|) xs) ⊢ e ∶ ((σ <|) t)
<|-⊢-∶ σ top = top
<|-⊢-∶ σ {xs} (var x) = var (<|-∋ σ xs x)
<|-⊢-∶ σ (fst ⊢e) = fst (<|-⊢-∶ σ ⊢e)
<|-⊢-∶ σ (snd ⊢e) = snd (<|-⊢-∶ σ ⊢e)
<|-⊢-∶ σ (inl ⊢e) = inl (<|-⊢-∶ σ ⊢e)
<|-⊢-∶ σ (inr ⊢e) = inr (<|-⊢-∶ σ ⊢e)
<|-⊢-∶ σ (⊢e ‵, ⊢f) = (<|-⊢-∶ σ ⊢e) ‵, (<|-⊢-∶ σ ⊢f)

<|-⊢ : (σ : Fin m → Type l) {xs : Vec (Type m) n} {P : Proc n} → xs ⊢ P → ((σ <|) xs) ⊢ P
<|-⊢ σ end = end
<|-⊢ σ (new t ⊢P) = new _ (<|-⊢ σ ⊢P)
<|-⊢ σ (comp ⊢P ⊢Q) = comp (<|-⊢ σ ⊢P) (<|-⊢ σ ⊢Q)
<|-⊢ σ (recv e ⊢P) = recv (<|-⊢-∶ σ e) (<|-⊢ σ ⊢P)
<|-⊢ σ (send e f ⊢P) = send (<|-⊢-∶ σ e) (<|-⊢-∶ σ f) (<|-⊢ σ ⊢P)
<|-⊢ σ (case e ⊢P ⊢Q) = case (<|-⊢-∶ σ e) (<|-⊢ σ ⊢P) (<|-⊢ σ ⊢Q)


unify-⊢ : {xs : Vec (Type m) n} {ys : Vec (Type l) n} (lhs rhs : Vec (Type m) k) {P : Proc n}
        → xs ⊢ P → unify-apply lhs rhs xs ≡ just (l , ys) → ys ⊢ P
unify-⊢ lhs rhs ⊢P eq with unify lhs rhs
unify-⊢ lhs rhs ⊢P refl | just (_ , σ) = <|-⊢ (sub σ) ⊢P

{-
merge-⊢ : (xs : Ctx n l) (ys : Ctx n m) {zs : Ctx n k}
        → unify-apply ((|> left-inject <|) xs) ((|> right-raise <|) ys) ((|> left-inject <|) xs) ≡ just (k , zs)
        → unify-apply ((|> left-inject <|) xs) ((|> right-raise <|) ys) ((|> right-raise <|) ys) ≡ just (k , zs)
merge-⊢ xs ys eq
  with just σ ← unify ((|> left-inject <|) xs) ((|> right-raise <|) ys)
     | I[ req ] ← inspect (unify ((|> left-inject <|) xs)) ((|> right-raise <|) ys)
  rewrite sym (amgu-sound ((|> left-inject <|) xs) ((|> right-raise <|) ys) idSubst req)
  = eq
  -}

inferExpr-sound : {Γ : Ctx n l} (e : Expr n) {t : Type l}
                → inferExpr e ≡ just (! Γ , t)
                → Γ ⊢ e ∶ t
inferExpr-sound top refl = top
inferExpr-sound (var x) refl = var refl
inferExpr-sound (fst e) {t} eq
  with just (! Γ , t) ← inferExpr e | I[ qe ] ← inspect inferExpr e
  with just (! σ) ← unify <[ t ] [ var zero ‵× var (suc (zero {zero})) ]>
     | I[ teq ] ← inspect (unify <[ t ]) [ var zero ‵× var (suc (zero {zero})) ]>
  with refl ← eq
  with ra ← <|-⊢-∶ (sub σ) (<|-⊢-∶ (|> (λ i → Fin.inject≤ i (ℕₚ.m≤m+n _ 2) )) (inferExpr-sound e qe))
  rewrite unify-sound <[ t ] [ var zero ‵× var (suc (zero {zero})) ]> teq
  = fst ra
inferExpr-sound (snd e) eq
  with just (! Γ , t) ← inferExpr e | I[ qe ] ← inspect inferExpr e
  with just (! σ) ← unify <[ t ] [ var zero ‵× var (suc (zero {zero})) ]>
     | I[ teq ] ← inspect (unify <[ t ]) [ var zero ‵× var (suc (zero {zero})) ]>
  with refl ← eq
  with ra ← <|-⊢-∶ (sub σ) (<|-⊢-∶ (|> (λ i → Fin.inject≤ i (ℕₚ.m≤m+n _ 2) )) (inferExpr-sound e qe))
  rewrite unify-sound <[ t ] [ var zero ‵× var (suc (zero {zero})) ]> teq
  = snd ra
inferExpr-sound (inl e) eq
  with just (! Γ , t) ← inferExpr e | I[ qe ] ← inspect inferExpr e
  with refl ← eq
  = inl (<|-⊢-∶ (|> (λ i → Fin.inject≤ i (ℕₚ.m≤m+n _ 1) )) (inferExpr-sound e qe))
inferExpr-sound (inr e) eq
  with just (! Γ , t) ← inferExpr e | I[ qe ] ← inspect inferExpr e
  with refl ← eq
  = inr (<|-⊢-∶ (|> (Fin.raise 1)) (inferExpr-sound e qe))
inferExpr-sound (e ‵, f) eq
  with just (! Γ₁ , t) ← inferExpr e | I[ eql ] ← inspect inferExpr e
  with just (! Γ₂ , s) ← inferExpr f | I[ eqr ] ← inspect inferExpr f
  with just (! σ) ← unify <[ Γ₁ ] [ Γ₂ ]>
  | I[ ueq ] ← inspect (unify <[ Γ₁ ]) [ Γ₂ ]>
  with refl ← eq
  with l ← <|-⊢-∶ (sub σ) (<|-⊢-∶ (|> (λ i → Fin.inject≤ i (ℕₚ.m≤m+n _ _) )) (inferExpr-sound e eql))
  with r ← <|-⊢-∶ (sub σ) (<|-⊢-∶ (|> (Fin.raise _)) (inferExpr-sound f eqr))
  rewrite unify-sound <[ Γ₁ ] [ Γ₂ ]> ueq
  = l ‵, r


{-
infer-sound : (P : Proc n) {Γ : Ctx n l} → infer P ≡ just (l , Γ) → Γ ⊢ P

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

infer-sound (recv e P) eq
  with just (_ , s ∷ Γ) ← infer P | I[ eqP ] ← inspect infer P
  with just t ← inferExpr Γ e | I[ eqe ] ← inspect (inferExpr Γ) e
  with just (_ , σ) ← unify t (# (|> Fin.inject₁ <|) s)
       | I[ req ]   ← inspect (unify t) (# (|> Fin.inject₁ <|) s)
  with refl ← eq
  = recv {!<|-⊢-∶ (sub σ) {!!} (inferExpr-sound {!!} e {!eqe!})!}
         (<|-⊢ (sub σ) (<|-⊢ (|> Fin.inject₁) (infer-sound P eqP)))
  {-
  recv {!(trans {!(<|-lookup (sub σ) Γ)!} (unify-sound t _ req))!}
         (<|-⊢ (sub σ) (infer-sound P {!eqP!}))
         -}

infer-sound (send e f P) eq
  with just (_ , Γ) ← infer P | I[ eqP ] ← inspect infer P
  with just t ← inferExpr Γ e | I[ eqe ] ← inspect (inferExpr Γ) e
  with just s ← inferExpr Γ f | I[ eqf ] ← inspect (inferExpr Γ) f
  with just (_ , σ) ← unify t (# s)
     | I[ req ]     ← inspect (unify t) (# s)
  with refl ← eq
  = send {!(trans (<|-lookup (sub σ) Γ) (amgu-sound (Vec.lookup Γ x) _ _ req))!}
         {!(<|-lookup (sub σ) Γ)!}
         (<|-⊢ {!sub σ!} (infer-sound P {!eqP!}))
-}
