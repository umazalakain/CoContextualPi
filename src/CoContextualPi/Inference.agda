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

import Data.Maybe.Categorical as maybeCat
import Data.Nat.Properties as ℕₚ
import Data.Fin.Properties as Finₚ
import Data.Vec.Properties as Vecₚ

open import CoContextualPi.Types
open import CoContextualPi.TypeSystem

module CoContextualPi.Inference where

private
  variable
    n m l k : ℕ
    u v : Univ

private
  -- Help ourselves to some goodies
  open RawFunctor {{...}}
  open RawApplicative {{...}} hiding (_<$>_)
  open RawMonad {{...}} hiding (_<$>_; _⊛_)
  instance maybeFunctor = maybeCat.functor
  instance maybeMonad = maybeCat.monad
  instance maybeApplicative = maybeCat.applicative


fresh : Ctx n n
fresh {n = zero} = []
fresh {n = suc n} = var zero ∷ Vec.map ((|> suc) <|) fresh

infixr 2 !_
pattern !_ t = _ , t


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


_==_ = unify-sound

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


inferExpr : (e : Expr n) → Maybe (Σ[ m ∈ ℕ ] Σ[ t ∈ Type m ] Σ[ Γ ∈ Ctx n m ] Γ ⊢ e ∶ t)
inferExpr top      = return (! ‵⊤ , fresh , top)
inferExpr (var x)  = return (! Vec.lookup fresh x , fresh , var refl)
inferExpr (fst e)  = do ! t , Γ₁ , ⊢e ← inferExpr e
                        let shape = var zero ‵× var (suc (zero {zero}))
                        ! σ , sound ← <[ t ] == [ shape ]>
                        let ⊢e' = <|-⊢-∶ (sub σ) (<|-⊢-∶ (|> <<) ⊢e)
                        return (! [ var zero ]|> σ , σ <|[ Γ₁ ] , fst (subst (_ ⊢ _ ∶_) sound ⊢e'))
inferExpr (snd e)  = do ! t , Γ₁ , ⊢e ← inferExpr e
                        let shape = var zero ‵× var (suc (zero {zero}))
                        ! σ , sound ← <[ t ] == [ shape ]>
                        let ⊢e' = <|-⊢-∶ (sub σ) (<|-⊢-∶ (|> <<) ⊢e)
                        return (! [ var (suc zero) ]|> σ , σ <|[ Γ₁ ] , snd (subst (_ ⊢ _ ∶_) sound ⊢e'))
inferExpr (inl e)  = do ! t , Γ₁ , ⊢e ← inferExpr e
                        let ⊢e' = <|-⊢-∶ (|> <<) ⊢e
                        return (! <[ t ] ‵+ [ var (zero {zero}) ]> , <[ Γ₁ ] , inl ⊢e')
inferExpr (inr e)  = do ! t , Γ₁ , ⊢e ← inferExpr e
                       let ⊢e' = <|-⊢-∶ (|> >>) ⊢e
                       return (! <[ var (zero {zero}) ] ‵+ [_]> {m = 1} t , [ Γ₁ ]> , inr ⊢e')
inferExpr (e ‵, f) = do ! t , Γ₁ , ⊢e ← inferExpr e
                        ! s , Γ₂ , ⊢f ← inferExpr f
                        ! σ , sound ← <[ Γ₁ ] == [ Γ₂ ]>
                        let ⊢e' = <|-⊢-∶ (sub σ) (<|-⊢-∶ (|> <<) ⊢e)
                        let ⊢f' = <|-⊢-∶ (sub σ) (<|-⊢-∶ (|> >>) ⊢f)
                        return (! (σ <|[ t ]) ‵× ([ s ]|> σ) , σ <|[ Γ₁ ] , (⊢e' ‵, subst (_⊢ _ ∶ _) (sym sound) ⊢f'))



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
