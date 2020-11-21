open import Data.Maybe as Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Product as Product using (Σ; _×_; ∃-syntax; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Vec as Vec using (Vec; []; _∷_)

import Data.Nat.Properties as ℕₚ
import Data.Fin.Properties as Finₚ

open import CoContextualPi.Types
open import CoContextualPi.TypingRules
open import CoContextualPi.Unification

module CoContextualPi.Inference where

private
  variable
    n m l k : ℕ



Eq : ℕ → Set
Eq n = Type n × Type n


fresh : Ctx n n
fresh {n = zero} = []
fresh {n = suc n} = ′ zero ∷ Vec.map (|> suc <|_) fresh


[_]⇓ : AList m l → Ctx n m → Ctx n l
[ σ ]⇓ = Vec.map (sub σ <|_)


amgus : Vec (Eq m) n → AList m l → Maybe (Σ ℕ (AList m))
amgus [] acc = just (_ , acc)
amgus ((s , t) ∷ eqs) acc = do _ , acc' ← amgu s t acc
                               amgus eqs acc'


unify : Vec (Eq m) n → Maybe (Σ ℕ (AList m))
unify eqs = amgus eqs []


unify-apply : Vec (Eq m) l → Ctx n m → Maybe (Σ ℕ (Ctx n))
unify-apply eqs Γ = do (_ , σ) ← unify eqs
                       just (_ , [ σ ]⇓ Γ)


left-inject : Fin m → Fin (m ℕ.⊔ n)
left-inject x = Fin.inject≤ x (ℕₚ.m≤m⊔n _ _)


right-inject : Fin n → Fin (m ℕ.⊔ n)
right-inject x = Fin.inject≤ x (ℕₚ.n≤m⊔n _ _)


merge : Ctx n l → Ctx n m → Vec (Eq (l ℕ.⊔ m)) n
merge xs ys = Vec.zip (Vec.map (|> left-inject <|_) xs) (Vec.map (|> right-inject <|_) ys)


merge-solve : Ctx n m → Ctx n l → Maybe (Σ ℕ (Ctx n))
merge-solve xs ys = unify-apply (merge xs ys) (Vec.map (|> left-inject <|_) xs)


infer : (p : Process n) → Maybe (Σ ℕ (Ctx n))
infer end = just (_ , fresh)
infer (new p) = do (_ , _ ∷ Γ) ← infer p
                   just (_ , Γ)
infer (comp p q) = do _ , Γ₁ ← infer p
                      _ , Γ₂ ← infer q
                      merge-solve Γ₁ Γ₂
infer (recv x p) = do _ , (y ∷ Γ) ← infer p
                      unify-apply ((Vec.lookup Γ x , # y) ∷ []) Γ
infer (send x y p) = do _ , Γ ← infer p
                        unify-apply ((Vec.lookup Γ x , # Vec.lookup Γ y) ∷ []) Γ
