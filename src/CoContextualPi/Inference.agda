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

shape : (∀ {n} → Type n → Type n → Type n) → Type (suc (suc m))
shape f = f (var zero) (var (suc zero))

unify-apply : UType u m → UType u m → ∀ {v} → UType v m → Maybe (Σ ℕ (UType v))
unify-apply xs ys Γ = do _ , σ ← unify xs ys
                         return (_ , ((sub σ <|) Γ) )


left-inject : Fin m → Fin (m ℕ.+ n)
left-inject x = Fin.inject≤ x (ℕₚ.m≤m+n _ _)


right-raise : Fin n → Fin (m ℕ.+ n)
right-raise = Fin.raise _


_==_ : UType u n → UType u m → Maybe (∃[ l ] ((∀ {v} → UType v n → UType v l)
                                           ×  (∀ {v} → UType v m → UType v l)))
(x == y) = do (_ , σ) ← unify ((|> left-inject <|) x) ((|> right-raise <|) y)
              return (_ , (λ {_} → (sub σ ∘ left-inject) <|) , (λ {_} → (sub σ ∘ right-raise) <|))


inferExpr : Expr n → Maybe (∃[ m' ] (Ctx n m' × Type m'))
inferExpr top      = just (_ , fresh , ‵⊤)
inferExpr (var x)  = just (_ , fresh , Vec.lookup fresh x)
inferExpr (fst e)  = do _ , Γ₁ , t ← inferExpr e
                        _ , fromLeft , fromRight ← t == shape {zero} _‵×_
                        return (_ , fromLeft Γ₁ , fromRight (var zero))
inferExpr (snd e)  = do _ , Γ₁ , t ← inferExpr e
                        let shape = var zero ‵× var (suc (zero {zero}))
                        _ , fromLeft , fromRight ← t == shape
                        return (_ , fromLeft Γ₁ , fromRight {one} (var (suc zero)))
inferExpr (inl e)  = do _ , Γ' , t ← inferExpr e
                        return (_ , (|> suc <|) Γ' , (|> suc <|) t ‵+ var zero)
inferExpr (inr e)  = do _ , Γ' , t ← inferExpr e
                        return (_ , (|> suc <|) Γ' , var zero ‵+ (|> suc <|) t)
inferExpr (e ‵, f) = do _ , Γ₁ , t ← inferExpr e
                        _ , Γ₂ , s ← inferExpr f
                        _ , fromLeft , fromRight ← Γ₁ == Γ₂
                        return (_ , fromLeft Γ₁ , fromLeft t ‵× fromRight s)


infer : (p : Proc n) → Maybe (Σ ℕ (Ctx n))
infer end          = just (_ , fresh)
infer (new p)      = do (_ , _ ∷ Γ) ← infer p
                        return (_ , Γ)
infer (comp p q)   = do _ , Γ₁ ← infer p
                        _ , Γ₂ ← infer q
                        _ , fromLeft , _ ← Γ₁ == Γ₂
                        return (_ , fromLeft Γ₁)
infer (recv e p)   = do _ , Γ₁ , c ← inferExpr e
                        _ , (v ∷ Γ₂) ← infer p
                        _ , fromLeft , _ ← (c ∷ Γ₁) == (# v ∷ Γ₂)
                        return (_ , fromLeft Γ₁)
infer (send e f p) = do _ , Γ₁ , c ← inferExpr e
                        _ , Γ₂ , v ← inferExpr f
                        _ , Γ₃ ← infer p
                        _ , fromLeft₁ , _ ← (c ∷ Γ₁) == (# v ∷ Γ₂)
                        _ , _ , fromRight₂ ← fromLeft₁ Γ₁ == Γ₃
                        return (_ , fromRight₂ Γ₃)
infer (case e p q) = do _ , Γ₁ , v ← inferExpr e
                        _ , (l ∷ Γ₂) ← infer p
                        _ , (r ∷ Γ₃) ← infer q
                        _ , fromLeft₁ , fromRight₁ ← Γ₂ == Γ₃
                        _ , fromLeft₂ , fromRight₂ ← (fromLeft₁ l ‵+ fromRight₁ r ∷ fromLeft₁ Γ₂) == (v ∷ Γ₁)
                        return (_ , fromRight₂ Γ₁)
