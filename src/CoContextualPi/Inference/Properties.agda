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

inferExpr-sound : {Γ : Ctx n l} (e : Expr n) {t : Type l}
                → inferExpr e ≡ just (! t , Γ)
                → Γ ⊢ e ∶ t
inferExpr-sound top refl = top
inferExpr-sound (var x) refl = var refl
inferExpr-sound (fst e) {t} eq
  with just (! t , Γ) ← inferExpr e | I[ qe ] ← inspect inferExpr e
  with just (! σ) ← unify <[ t ] [ var zero ‵× var (suc (zero {zero})) ]>
     | I[ teq ] ← inspect (unify <[ t ]) [ var zero ‵× var (suc (zero {zero})) ]>
  with refl ← eq
  with ra ← <|-⊢-∶ (sub σ) (<|-⊢-∶ (|> <<) (inferExpr-sound e qe))
  rewrite unify-sound <[ t ] [ var zero ‵× var (suc (zero {zero})) ]> teq
  = fst ra
inferExpr-sound (snd e) eq
  with just (! t , Γ) ← inferExpr e | I[ qe ] ← inspect inferExpr e
  with just (! σ) ← unify <[ t ] [ var zero ‵× var (suc (zero {zero})) ]>
     | I[ teq ] ← inspect (unify <[ t ]) [ var zero ‵× var (suc (zero {zero})) ]>
  with refl ← eq
  with ra ← <|-⊢-∶ (sub σ) (<|-⊢-∶ (|> <<) (inferExpr-sound e qe))
  rewrite unify-sound <[ t ] [ var zero ‵× var (suc (zero {zero})) ]> teq
  = snd ra
inferExpr-sound (inl e) eq
  with just (! Γ , t) ← inferExpr e | I[ qe ] ← inspect inferExpr e
  with refl ← eq
  = inl (<|-⊢-∶ (|> <<) (inferExpr-sound e qe))
inferExpr-sound (inr e) eq
  with just (! Γ , t) ← inferExpr e | I[ qe ] ← inspect inferExpr e
  with refl ← eq
  = inr (<|-⊢-∶ (|> >>) (inferExpr-sound e qe))
inferExpr-sound (e ‵, f) eq
  with just (! t , Γ₁) ← inferExpr e | I[ eql ] ← inspect inferExpr e
  with just (! s , Γ₂) ← inferExpr f | I[ eqr ] ← inspect inferExpr f
  with just (! σ) ← unify <[ Γ₁ ] [ Γ₂ ]>
  | I[ ueq ] ← inspect (unify <[ Γ₁ ]) [ Γ₂ ]>
  with refl ← eq
  with l ← <|-⊢-∶ (sub σ) (<|-⊢-∶ (|> <<) (inferExpr-sound e eql))
  with r ← <|-⊢-∶ (sub σ) (<|-⊢-∶ (|> >>) (inferExpr-sound f eqr))
  rewrite unify-sound <[ Γ₁ ] [ Γ₂ ]> ueq
  = l ‵, r


infer-sound : (P : Proc n) {Γ : Ctx n l} → infer P ≡ just (l , Γ) → Γ ⊢ P

infer-sound end eq = end

infer-sound (new P) eq
  with just (! t ∷ Γ) ← infer P | I[ qe ] ← inspect infer P
  with refl ← eq
  = new t (infer-sound P qe)

infer-sound (comp P Q) eq
  with just (! Γ₁) ← infer P | I[ eqP ] ← inspect infer P
  with just (! Γ₂) ← infer Q | I[ eqQ ] ← inspect infer Q
  with just (! σ) ← unify <[ Γ₁ ] [ Γ₂ ]>
     | I[ eqU ]   ← inspect (unify <[ Γ₁ ]) [ Γ₂ ]>
  with refl ← eq
  with l ← <|-⊢ (sub σ) (<|-⊢ (|> <<) (infer-sound P eqP))
  with r ← <|-⊢ (sub σ) (<|-⊢ (|> >>) (infer-sound Q eqQ))
  rewrite unify-sound <[ Γ₁ ] [ Γ₂ ]> eqU
  = comp l r

infer-sound (recv e P) eq
  with just (! c , Γ₁) ← inferExpr e | I[ eqe ] ← inspect inferExpr e
  with just (! v ∷ Γ₂) ← infer P | I[ eqP ] ← inspect infer P
  with just (! σ) ← unify <[ c ∷ Γ₁ ] [ # v ∷ Γ₂ ]>
     | I[ eqU ]   ← inspect (unify <[ c ∷ Γ₁ ]) [ # v ∷ Γ₂ ]>
  with refl ← eq
  with e' ← <|-⊢-∶ (sub σ) (<|-⊢-∶ (|> <<) (inferExpr-sound e eqe))
  with P' ← <|-⊢ (sub σ) (<|-⊢ (|> >>) (infer-sound P eqP))
  with uS ← unify-sound <[ c ∷ Γ₁ ] [ # v ∷ Γ₂ ]> eqU
  rewrite Vecₚ.∷-injectiveˡ uS
  rewrite Vecₚ.∷-injectiveʳ uS
  = recv e' P'

infer-sound (send e f P) eq
  with just (! c , Γ₁) ← inferExpr e | I[ eqe ] ← inspect inferExpr e
  with just (! v , Γ₂) ← inferExpr f | I[ eqf ] ← inspect inferExpr f
  with just (! Γ₃) ← infer P | I[ eqP ] ← inspect infer P
  with just (! σ₁) ← unify <[ c ∷ Γ₁ ] [ # v ∷ Γ₂ ]>
     | I[ eqU₁ ]   ← inspect (unify <[ c ∷ Γ₁ ]) [ # v ∷ Γ₂ ]>
  with just (! σ₂) ← unify <[ σ₁ <|[ Γ₁ ] ] [ Γ₃ ]>
     | I[ eqU₂ ]   ← inspect (unify <[ σ₁ <|[ Γ₁ ] ]) [ Γ₃ ]>
  with refl ← eq
  with e' ← <|-⊢-∶ (sub σ₂) (<|-⊢-∶ (|> <<) (<|-⊢-∶ (sub σ₁) (<|-⊢-∶ (|> <<) (inferExpr-sound e eqe))))
  with f' ← <|-⊢-∶ (sub σ₂) (<|-⊢-∶ (|> <<) (<|-⊢-∶ (sub σ₁) (<|-⊢-∶ (|> >>) (inferExpr-sound f eqf))))
  with P' ← <|-⊢ (sub σ₂) (<|-⊢ (|> >>) (infer-sound P eqP))
  rewrite sym (unify-sound <[ σ₁ <|[ Γ₁ ] ] [ Γ₃ ]> eqU₂)
  with uS₁ ← unify-sound <[ c ∷ Γ₁ ] [ # v ∷ Γ₂ ]> eqU₁
  rewrite Vecₚ.∷-injectiveˡ uS₁
  rewrite Vecₚ.∷-injectiveʳ uS₁
  = send e' f' P'

infer-sound (case e P Q) eq
  with just (! v , Γ₁) ← inferExpr e | I[ eqe ] ← inspect inferExpr e
  with just (! l ∷ Γ₂) ← infer P | I[ eqP ] ← inspect infer P
  with just (! r ∷ Γ₃) ← infer Q | I[ eqQ ] ← inspect infer Q
  with just (! σ₁) ← unify <[ Γ₂ ] [ Γ₃ ]>
     | I[ eqU₁ ]   ← inspect (unify <[ Γ₂ ]) [ Γ₃ ]>
  with just (! σ₂) ← unify <[ (σ₁ <|[ l ]) ‵+ ([ r ]|> σ₁) ∷ σ₁ <|[ Γ₂ ] ] [ v ∷ Γ₁ ]>
     | I[ eqU₂ ]   ← inspect (unify <[ (σ₁ <|[ l ]) ‵+ ([ r ]|> σ₁) ∷ σ₁ <|[ Γ₂ ] ]) [ v ∷ Γ₁ ]>
  with refl ← eq
  with e' ← <|-⊢-∶ (sub σ₂) (<|-⊢-∶ (|> >>) (inferExpr-sound e eqe))
  with P' ← <|-⊢ (sub σ₂) (<|-⊢ (|> <<) (<|-⊢ (sub σ₁) (<|-⊢ (|> <<) (infer-sound P eqP))))
  with Q' ← <|-⊢ (sub σ₂) (<|-⊢ (|> <<) (<|-⊢ (sub σ₁) (<|-⊢ (|> >>) (infer-sound Q eqQ))))
  with uS₂ ← unify-sound <[ (σ₁ <|[ l ]) ‵+ ([ r ]|> σ₁) ∷ σ₁ <|[ Γ₂ ] ] [ v ∷ Γ₁ ]> eqU₂
  rewrite sym (Vecₚ.∷-injectiveˡ uS₂)
  rewrite sym (Vecₚ.∷-injectiveʳ uS₂)
  rewrite sym (unify-sound <[ Γ₂ ] [ Γ₃ ]> eqU₁)
  = case e' P' Q'
