open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym; subst; subst₂)
open import Category.Functor
open import Category.Monad
open import Category.Applicative
open import Function using (_∘_)

open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product as Product using (Σ; _×_; ∃-syntax; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Vec as Vec using (Vec; []; _∷_; [_])
open import Data.List as List using (List; []; _∷_; [_])

import Data.Maybe.Categorical as maybeCat
import Data.Nat.Properties as ℕₚ
import Data.Fin.Properties as Finₚ
import Data.Vec.Properties as Vecₚ

open import CoContextualPi.Types
open Unification using (|>; _<|_; var; con; zero; suc; !_)
open import CoContextualPi.TypeSystem

module CoContextualPi.Inference where

private
  variable
    n m l : ℕ
    k k' : Kind
    γ δ : KindCtx
    x y z : Usage γ
    t s r : Type γ
    Γ Δ Θ : Ctx n γ

private
  -- Help ourselves to some goodies
  open RawFunctor {{...}}
  open RawApplicative {{...}} hiding (_<$>_)
  open RawMonad {{...}} hiding (_<$>_; _⊛_)
  instance maybeFunctor = maybeCat.functor
  instance maybeMonad = maybeCat.monad
  instance maybeApplicative = maybeCat.applicative


suc-≔-+₀ : x ≔ y +₀ z → (|> (Product.map _ (suc {k' = k'})) <|_) x ≔ (|> (Product.map _ suc) <|_) y +₀ (|> (Product.map _ suc) <|_) z
suc-≔-+₀ erased = erased
suc-≔-+₀ 1-left = 1-left
suc-≔-+₀ 1-right = 1-right
suc-≔-+₀ shared = shared

suc-≔-+₁ : t ≔ s +₁ r → (|> (Product.map _ (suc {k' = k'})) <|_) t ≔ (|> (Product.map _ suc) <|_) s +₁ (|> (Product.map _ suc) <|_) r
suc-≔-+₁ var = var
suc-≔-+₁ top = top
suc-≔-+₁ (chan i o) = chan (suc-≔-+₀ i) (suc-≔-+₀ o)
suc-≔-+₁ (prod l r) = prod (suc-≔-+₁ l) (suc-≔-+₁ r)
suc-≔-+₁ (sum l r) = sum (suc-≔-+₁ l) (suc-≔-+₁ r)

suc-≔-+₂ : Γ ≔ Δ +₂ Θ → Vec.map (|> (Product.map _ (suc {k' = k'})) <|_) Γ ≔ Vec.map (|> (Product.map _ suc) <|_) Δ +₂ Vec.map (|> (Product.map _ suc) <|_) Θ
suc-≔-+₂ [] = []
suc-≔-+₂ (x ∷ xs) = suc-≔-+₁ x ∷ suc-≔-+₂ xs

fresh : ∃[ γ ] (Σ (Ctx n γ) un₂)
fresh {n = zero} = [] , [] , []
fresh {n = suc n} = let γ , Γ , unΓ = fresh {n = n} in
  type ∷ γ , var (! zero) ∷ Vec.map (|> (Product.map _ suc) <|_) Γ , var ∷ suc-≔-+₂ unΓ

infixr 2 !_
pattern !_ t = _ , t

<|-∋-▹-lookup : {xs : Vec (Type γ) (suc n)} (x : Fin (suc n))
              → ∃[ ys ] (xs ∋ x ∶ Vec.lookup xs x ▹ ys)
<|-∋-▹-lookup {xs = _ ∷ _} zero = ! zero
<|-∋-▹-lookup {n = suc _} {xs = _ ∷ _} (suc x) = Product.map _ suc (<|-∋-▹-lookup x)

{-
<|-∋-▹ : (σ : ∀ {k} → γ Unification.∋ k → δ Unification.⊢ k)
       → {xs : Vec (Type γ) (suc n)} {ys : Vec (Type γ) n} {x : Fin (suc n)} {t : Type γ}
       → xs ∋ x ∶ t ▹ ys → Vec.map (σ <|_) xs ∋ x ∶ (σ <| t) ▹ Vec.map (σ <|_) ys
<|-∋-▹ σ zero = zero
<|-∋-▹ σ (suc x) = suc (<|-∋-▹ σ x)

<|-∋ : (σ : ∀ {k} → γ Unification.∋ k → δ Unification.⊢ k)
     → (xs : Vec (Type γ) (suc n)) {x : Fin (suc n)} {t : Type γ}
     → xs ∋ x ∶ t → Vec.map (σ <|_) xs ∋ x ∶ (σ <| t)
<|-∋ σ xs (fst₁ , x , snd₁) = {!!} , <|-∋-▹ σ x , {!!}
-}

{-
<|-⊢-∶ : (σ : Fin m → Type l) {xs : Vec (Type m) n} {e : Expr n} {t : Type m}
       → xs ⊢ e ∶ t → (σ <| xs) ⊢ e ∶ (σ <| t)
<|-⊢-∶ σ top = top
<|-⊢-∶ σ {xs} (var x) = var (<|-∋ σ xs x)
<|-⊢-∶ σ (fst ⊢e) = fst (<|-⊢-∶ σ ⊢e)
<|-⊢-∶ σ (snd ⊢e) = snd (<|-⊢-∶ σ ⊢e)
<|-⊢-∶ σ (inl ⊢e) = inl (<|-⊢-∶ σ ⊢e)
<|-⊢-∶ σ (inr ⊢e) = inr (<|-⊢-∶ σ ⊢e)
<|-⊢-∶ σ (⊢e ‵, ⊢f) = (<|-⊢-∶ σ ⊢e) ‵, (<|-⊢-∶ σ ⊢f)

<|-⊢ : (σ : Fin m → Type l) {xs : Vec (Type m) n} {P : Proc n} → xs ⊢ P → (σ <| xs) ⊢ P
<|-⊢ σ end = end
<|-⊢ σ (new t ⊢P) = new _ (<|-⊢ σ ⊢P)
<|-⊢ σ (comp ⊢P ⊢Q) = comp (<|-⊢ σ ⊢P) (<|-⊢ σ ⊢Q)
<|-⊢ σ (recv e ⊢P) = recv (<|-⊢-∶ σ e) (<|-⊢ σ ⊢P)
<|-⊢ σ (send e f ⊢P) = send (<|-⊢-∶ σ e) (<|-⊢-∶ σ f) (<|-⊢ σ ⊢P)
<|-⊢ σ (case e ⊢P ⊢Q) = case (<|-⊢-∶ σ e) (<|-⊢ σ ⊢P) (<|-⊢ σ ⊢Q)
-}

_==_ = Unificationₚ.unify-sound

{-
<< : Fin n → Fin (n ℕ.+ m)
<< i = Fin.inject≤ i (ℕₚ.m≤m+n _ _)

>> : Fin n → Fin (m ℕ.+ n)
>> = Fin.raise _

<[_] : UType u n → UType u (n ℕ.+ m)
<[_] = |> << <|

_<|[_] : Subst (n ℕ.+ m) l → UType u n → UType u l
_<|[_] σ = (sub σ) <| ∘ <[_]

[_]> : UType u n → UType u (m ℕ.+ n)
[_]> = |> >> <|

[_]|>_ : UType u m → Subst (n ℕ.+ m) l → UType u l
[_]|>_ x σ = ((sub σ) <|) [ x ]>

-}

inferExpr : (e : Expr n) → Maybe (Σ[ γ ∈ KindCtx ] Σ[ t ∈ Type γ ] Σ[ Γ ∈ Ctx n γ ] Γ ⊢ e ∶ t)
inferExpr top      = do let γ , Γ , unΓ = fresh
                        return (! ‵⊤ , Γ , top unΓ)
inferExpr {n = suc _} (var x)  = do let γ , Γ , unΓ = fresh
                                    let ! ∋x = <|-∋-▹-lookup x
                                    return ((! Vec.lookup Γ x , Γ , var (! ∋x , {!unΓ!})))
inferExpr (fst e)  = do ! t , Γ₁ , ⊢e ← inferExpr e
                        let shape = var (! zero) ‵× var (! suc zero)
                        ! σ , sound ← {!<[ t ]!} == {![ shape ]>!}
                        let ⊢e' = {!<|-⊢-∶ (sub σ) (<|-⊢-∶ (|> {!<<!}) ⊢e)!}
                        return {!(! [ var zero ]|> σ , σ <|[ Γ₁ ] , fst (subst (_ ⊢ _ ∶_) sound ⊢e'))!}
inferExpr (snd e)  = do ! t , Γ₁ , ⊢e ← inferExpr e
                        let shape = var (_ , zero) ‵× var (_ , suc zero)
                        ! σ , sound ← {!<[ t ]!} == {![ shape ]>!}
                        let ⊢e' = {!<|-⊢-∶ (sub σ) (<|-⊢-∶ (|> {!<<!}) ⊢e)!}
                        return {!(! [ var (suc zero) ]|> σ , σ <|[ Γ₁ ] , snd (subst (_ ⊢ _ ∶_) sound ⊢e'))!}
inferExpr (inl e)  = do ! t , Γ₁ , ⊢e ← inferExpr e
                        let ⊢e' = {!<|-⊢-∶ (|> {!<<!}) ⊢e!}
                        return {!(! <[ t ] ‵+ [ var (zero {zero}) ]> , <[ Γ₁ ] , inl ⊢e')!}
inferExpr (inr e)  = do ! t , Γ₁ , ⊢e ← inferExpr e
                        let ⊢e' = {!<|-⊢-∶ (|> {!>>!}) ⊢e!}
                        return {!(! <[ var (zero {zero}) ] ‵+ [_]> {m = 1} t , [ Γ₁ ]> , inr ⊢e')!}
inferExpr (e ‵, f) = do ! t , Γ₁ , ⊢e ← inferExpr e
                        ! s , Γ₂ , ⊢f ← inferExpr f
                        ! σ , sound ← {!<[ Γ₁ ]!} == {![ Γ₂ ]>!}
                        let ⊢e' = {!<|-⊢-∶ (sub σ) (<|-⊢-∶ (|> {!<<!}) ⊢e)!}
                        let ⊢f' = {!<|-⊢-∶ (sub σ) (<|-⊢-∶ (|> {!>>!}) ⊢f)!}
                        return {!(! (σ <|[ t ]) ‵× ([ s ]|> σ) , σ <|[ Γ₁ ] , (⊢e' ‵, subst (_⊢ _ ∶ _) (sym sound) ⊢f'))!}


{-

infer : (p : Proc n) → Maybe (Σ[ m ∈ ℕ ] Σ[ Γ ∈ Ctx n m ] Γ ⊢ p)
infer end          = return (! fresh , end)
infer (new p)      = do ! t ∷ Γ , ⊢p ← infer p
                        return (! Γ , new t ⊢p)
infer (comp p q)   = do ! Γ₁ , ⊢p ← infer p
                        ! Γ₂ , ⊢q ← infer q
                        ! σ , sound ← <[ Γ₁ ] == [ Γ₂ ]>
                        let ⊢p' = <|-⊢ (sub σ) (<|-⊢ (|> <<) ⊢p)
                        let ⊢q' = <|-⊢ (sub σ) (<|-⊢ (|> >>) ⊢q)
                        return (! σ <|[ Γ₁ ] , comp ⊢p' (subst (_⊢ _) (sym sound) ⊢q'))
infer (recv e p)   = do ! c , Γ₁ , ⊢e ← inferExpr e
                        ! v ∷ Γ₂ , ⊢p ← infer p
                        ! σ , sound ← <[ c ∷ Γ₁ ] == [ # v ∷ Γ₂ ]>
                        let c#v-sound , Γ₁Γ₂-sound = Vecₚ.∷-injective sound
                        let ⊢e' = <|-⊢-∶ (sub σ) (<|-⊢-∶ (|> <<) ⊢e)
                        let ⊢p' = <|-⊢ (sub σ) (<|-⊢ (|> >>) ⊢p)
                        return (! σ <|[ Γ₁ ] , recv (subst (_ ⊢ _ ∶_) (c#v-sound) ⊢e')
                                                    (subst (λ ● → (_ ∷ ●) ⊢ _) (sym Γ₁Γ₂-sound) ⊢p'))
infer (send e f p) = do ! c , Γ₁ , ⊢e ← inferExpr e
                        ! v , Γ₂ , ⊢f ← inferExpr f
                        ! Γ₃ , ⊢p ← infer p
                        ! σ₁ , sound ← <[ c ∷ Γ₁ ] == [ # v ∷ Γ₂ ]>
                        ! σ₂ , Γ₁Γ₃-sound ← <[ σ₁ <|[ Γ₁ ] ] == [ Γ₃ ]>
                        let c#v-sound , Γ₁Γ₂-sound = Vecₚ.∷-injective sound
                        let ⊢e' = <|-⊢-∶ (sub σ₂) (<|-⊢-∶ (|> <<) (<|-⊢-∶ (sub σ₁) (<|-⊢-∶ (|> <<) ⊢e)))
                        let ⊢f' = <|-⊢-∶ (sub σ₂) (<|-⊢-∶ (|> <<) (<|-⊢-∶ (sub σ₁) (<|-⊢-∶ (|> >>) ⊢f)))
                        let ⊢p' = <|-⊢ (sub σ₂) (<|-⊢ (|> >>) ⊢p)
                        return (! [ Γ₃ ]|> σ₂ , send (subst₂ (_⊢ _ ∶_) Γ₁Γ₃-sound (cong (sub σ₂ <| ∘ |> << <|) c#v-sound) ⊢e')
                                                     (subst (_⊢ _ ∶ _) (trans (cong (sub σ₂ <| ∘ |> << <|) (sym Γ₁Γ₂-sound)) Γ₁Γ₃-sound) ⊢f')
                                                     ⊢p')
infer (case e p q) = do ! v , Γ₁ , ⊢e ← inferExpr e
                        ! l ∷ Γ₂ , ⊢p ← infer p
                        ! r ∷ Γ₃ , ⊢q ← infer q
                        ! σ₁ , Γ₂Γ₃-sound ← <[ Γ₂ ] == [ Γ₃ ]>
                        ! σ₂ , sound ← <[ v ∷ Γ₁ ] == [ (σ₁ <|[ l ]) ‵+ ([ r ]|> σ₁) ∷ σ₁ <|[ Γ₂ ] ]>
                        let lrv-sound , Γ₁Γ₂-sound = Vecₚ.∷-injective sound
                        let ⊢e' = <|-⊢-∶ (sub σ₂) (<|-⊢-∶ (|> <<) ⊢e)
                        let ⊢p' = <|-⊢ (sub σ₂) (<|-⊢ (|> >>) (<|-⊢ (sub σ₁) (<|-⊢ (|> <<) ⊢p)))
                        let ⊢q' = <|-⊢ (sub σ₂) (<|-⊢ (|> >>) (<|-⊢ (sub σ₁) (<|-⊢ (|> >>) ⊢q)))
                        return (! σ₂ <|[ Γ₁ ] , case (subst (_ ⊢ _ ∶_) lrv-sound ⊢e')
                                                     (subst (λ ● → (_ ∷ ●) ⊢ _) (sym Γ₁Γ₂-sound) ⊢p')
                                                     (subst (λ ● → (_ ∷ ●) ⊢ _) (sym (trans Γ₁Γ₂-sound (cong (sub σ₂ <| ∘ |> >> <|) Γ₂Γ₃-sound))) ⊢q'))
-}
