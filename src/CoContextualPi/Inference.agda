open import Data.Maybe as Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Product as Product using (Σ; _×_; ∃-syntax; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Vec as Vec using (Vec; []; _∷_; [_])

import Data.Nat.Properties as ℕₚ
import Data.Fin.Properties as Finₚ

open import CoContextualPi.Types
open import CoContextualPi.TypingRules
open import CoContextualPi.Unification

module CoContextualPi.Inference where

private
  variable
    n m l k : ℕ



fresh : Ctx n n
fresh {n = zero} = []
fresh {n = suc n} = ′ zero ∷ Vec.map (|> suc <|_) fresh



unify-apply : Vec (Type m) l → Vec (Type m) l → Ctx n m → Maybe (Σ ℕ (Ctx n))
unify-apply xs ys Γ = do (_ , σ) ← unify xs ys
                         just (_ , [ sub σ ]⇓ Γ)


left-inject : Fin m → Fin (m ℕ.⊔ n)
left-inject x = Fin.inject≤ x (ℕₚ.m≤m⊔n _ _)


right-inject : Fin n → Fin (m ℕ.⊔ n)
right-inject x = Fin.inject≤ x (ℕₚ.n≤m⊔n _ _)


merge : Ctx n m → Ctx n l → Maybe (Σ ℕ (Ctx n))
merge xs ys = unify-apply ([ |> left-inject ]⇓ xs)
                          ([ |> right-inject ]⇓ ys)
                          ([ |> left-inject ]⇓ xs)


infer : (p : Process n) → Maybe (Σ ℕ (Ctx n))
infer end = just (_ , fresh)
infer (new p) = do (_ , _ ∷ Γ) ← infer p
                   just (_ , Γ)
infer (comp p q) = do _ , Γ₁ ← infer p
                      _ , Γ₂ ← infer q
                      merge Γ₁ Γ₂
infer (recv x p) = do _ , (y ∷ Γ) ← infer p
                      unify-apply [ Vec.lookup Γ x ] [ # y ] Γ
infer (send x y p) = do _ , Γ ← infer p
                        unify-apply [ Vec.lookup Γ x ] [ # Vec.lookup Γ y ] Γ
