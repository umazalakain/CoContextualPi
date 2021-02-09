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


left-inject : Fin m → Fin (m ℕ.+ n)
left-inject x = Fin.inject≤ x (ℕₚ.m≤m+n _ _)


right-raise : Fin n → Fin (m ℕ.+ n)
right-raise = Fin.raise _


_==_ : UType u n → UType u m → Maybe (∃[ l ] ((∀ {v} → UType v n → UType v l)
                                           ×  (∀ {v} → UType v m → UType v l)))
(x == y) = do ! σ ← unify ((|> left-inject <|) x) ((|> right-raise <|) y)
              return (! (λ {_} → (sub σ ∘ left-inject) <|)
                      , (λ {_} → (sub σ ∘ right-raise) <|))


inferExpr : Expr n → Maybe (∃[ m' ] (Ctx n m' × Type m'))
inferExpr top      = return (! fresh , ‵⊤)
inferExpr (var x)  = return (! fresh , Vec.lookup fresh x)
inferExpr (fst e)  = do ! Γ₁ , t ← inferExpr e
                        let shape = var zero ‵× var (suc (zero {zero}))
                        ! fromLeft , fromRight ← t == shape
                        return (! fromLeft Γ₁ , fromRight (var zero))
inferExpr (snd e)  = do ! Γ₁ , t ← inferExpr e
                        let shape = var zero ‵× var (suc (zero {zero}))
                        ! fromLeft , fromRight ← t == shape
                        return (! fromLeft Γ₁ , fromRight {one} (var (suc zero)))
inferExpr (inl e)  = do ! Γ' , t ← inferExpr e
                        return (! (|> suc <|) Γ' , (|> suc <|) t ‵+ var zero)
inferExpr (inr e)  = do ! Γ' , t ← inferExpr e
                        return (! (|> suc <|) Γ' , var zero ‵+ (|> suc <|) t)
inferExpr (e ‵, f) = do ! Γ₁ , t ← inferExpr e
                        ! Γ₂ , s ← inferExpr f
                        ! fromLeft , fromRight ← Γ₁ == Γ₂
                        return (! fromLeft Γ₁ , fromLeft t ‵× fromRight s)


infer : (p : Proc n) → Maybe (Σ ℕ (Ctx n))
infer end          = return (! fresh)
infer (new p)      = do ! _ ∷ Γ ← infer p
                        return (! Γ)
infer (comp p q)   = do ! Γ₁ ← infer p
                        ! Γ₂ ← infer q
                        ! fromLeft , _ ← Γ₁ == Γ₂
                        return (! fromLeft Γ₁)
infer (recv e p)   = do ! Γ₁ , c ← inferExpr e
                        ! (v ∷ Γ₂) ← infer p
                        ! fromLeft , _ ← (c ∷ Γ₁) == (# v ∷ Γ₂)
                        return (! fromLeft Γ₁)
infer (send e f p) = do ! Γ₁ , c ← inferExpr e
                        ! Γ₂ , v ← inferExpr f
                        ! Γ₃ ← infer p
                        ! fromLeft₁ , _ ← (c ∷ Γ₁) == (# v ∷ Γ₂)
                        ! _ , fromRight₂ ← fromLeft₁ Γ₁ == Γ₃
                        return (! fromRight₂ Γ₃)
infer (case e p q) = do ! Γ₁ , v ← inferExpr e
                        ! (l ∷ Γ₂) ← infer p
                        ! (r ∷ Γ₃) ← infer q
                        ! fromLeft₁ , fromRight₁ ← Γ₂ == Γ₃
                        ! fromLeft₂ , fromRight₂ ← (fromLeft₁ l ‵+ fromRight₁ r ∷ fromLeft₁ Γ₂) == (v ∷ Γ₁)
                        return (! fromRight₂ Γ₁)
