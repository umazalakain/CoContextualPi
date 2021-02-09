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

unify-apply : UType u m → UType u m → ∀ {v} → UType v m → Maybe (Σ ℕ (UType v))
unify-apply xs ys Γ = do _ , σ ← unify xs ys
                         return (_ , ((sub σ <|) Γ) )


_==_ = unify

<[_] : UType u n → UType u (n ℕ.+ m)
<[ x ] = (|> (λ i → Fin.inject≤ i (ℕₚ.m≤m+n _ _)) <|) x

_<|[_] : Subst (n ℕ.+ m) l → UType u n → UType u l
_<|[_] σ = sub σ <| ∘ <[_]

[_]> : UType u n → UType u (m ℕ.+ n)
[ x ]> = (|> (Fin.raise _) <|) x

[_]|>_ : UType u m → Subst (n ℕ.+ m) l → UType u l
[_]|>_ x σ = (sub σ <|) [ x ]>


inferExpr : Expr n → Maybe (∃[ m ] (Ctx n m × Type m))
inferExpr top      = return (! fresh , ‵⊤)
inferExpr (var x)  = return (! fresh , Vec.lookup fresh x)
inferExpr (fst e)  = do ! Γ₁ , t ← inferExpr e
                        let shape = var zero ‵× var (suc (zero {zero}))
                        ! σ ← <[ t ] == [ shape ]>
                        return (! σ <|[ Γ₁ ] , [ var zero ]|> σ)
inferExpr (snd e)  = do ! Γ₁ , t ← inferExpr e
                        let shape = var zero ‵× var (suc (zero {zero}))
                        ! σ ← <[ t ] == [ shape ]>
                        return (! σ <|[ Γ₁ ] , [ var (suc zero) ]|> σ)
inferExpr (inl e)  = do ! Γ' , t ← inferExpr e
                        return (! (<[ Γ' ] , <[ t ] ‵+ [ var (zero {zero}) ]> ))
inferExpr (inr e)  = do ! Γ' , t ← inferExpr e
                        return (! ([ Γ' ]> , <[ var (zero {zero}) ] ‵+ [_]> {m = 1} t ))
inferExpr (e ‵, f) = do ! Γ₁ , t ← inferExpr e
                        ! Γ₂ , s ← inferExpr f
                        ! σ ← <[ Γ₁ ] == [ Γ₂ ]>
                        return (! σ <|[ Γ₁ ] , (σ <|[ t ]) ‵× ([ s ]|> σ))


infer : (p : Proc n) → Maybe (Σ ℕ (Ctx n))
infer end          = return (! fresh)
infer (new p)      = do ! _ ∷ Γ ← infer p
                        return (! Γ)
infer (comp p q)   = do ! Γ₁ ← infer p
                        ! Γ₂ ← infer q
                        ! σ ← <[ Γ₁ ] == [ Γ₂ ]>
                        return (! σ <|[ Γ₁ ])
infer (recv e p)   = do ! Γ₁ , c ← inferExpr e
                        ! (v ∷ Γ₂) ← infer p
                        ! σ ← <[ c ∷ Γ₁ ] == [ # v ∷ Γ₂ ]>
                        return (! σ <|[ Γ₁ ])
infer (send e f p) = do ! Γ₁ , c ← inferExpr e
                        ! Γ₂ , v ← inferExpr f
                        ! Γ₃ ← infer p
                        ! σ₁ ← <[ c ∷ Γ₁ ] == [ # v ∷ Γ₂ ]>
                        ! σ₂ ← <[ σ₁ <|[ Γ₁ ] ] == [ Γ₃ ]>
                        return (! [ Γ₃ ]|> σ₂)
infer (case e p q) = do ! Γ₁ , v ← inferExpr e
                        ! (l ∷ Γ₂) ← infer p
                        ! (r ∷ Γ₃) ← infer q
                        ! σ₁ ← <[ Γ₂ ] == [ Γ₃ ]>
                        ! σ₂ ← <[ (σ₁ <|[ l ]) ‵+ ([ r ]|> σ₁) ∷ σ₁ <|[ Γ₂ ] ] == [ v ∷ Γ₁ ]>
                        return (! [ Γ₁ ]|> σ₂)
