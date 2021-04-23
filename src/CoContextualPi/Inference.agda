open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym; subst; subst₂; cong-app; cong₂)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (id)
open import Function.Reasoning using () renaming (_|>_ to _|>>_)
open import Category.Functor
open import Category.Monad
open import Category.Applicative
open import Function using (_∘_)

open import Data.Unit as Unit using (⊤; tt)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product as Product using (Σ; _×_; ∃-syntax; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Vec as Vec using (Vec; []; _∷_; [_])
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.List as List using (List; []; _∷_; [_])
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)

import Data.Maybe.Categorical as maybeCat
import Data.Nat.Properties as ℕₚ
import Data.Fin.Properties as Finₚ
import Data.Vec.Properties as Vecₚ
import Data.List.Properties as Listₚ
import Data.List.Relation.Unary.All.Properties as Allₚ

open import CoContextualPi.Types
open Unification using (|>; _<|_; var; con; zero; suc; !_)
open import CoContextualPi.TypeSystem

module CoContextualPi.Inference where

private
  variable
    u : Univ
    n m l : ℕ
    k k₁ k₂ k₃ : Kind
    γ δ θ ξ : KindCtx
    x y z i o iₗ iᵣ oₗ oᵣ : Usage γ
    t s r sₗ sᵣ tₗ tᵣ : Type γ
    Γ Δ Θ : Ctx n γ

private
  -- Help ourselves to some goodies
  open RawFunctor {{...}}
  open RawApplicative {{...}} hiding (_<$>_)
  open RawMonad {{...}} hiding (_<$>_; _⊛_)
  instance maybeFunctor = maybeCat.functor
  instance maybeMonad = maybeCat.monad
  instance maybeApplicative = maybeCat.applicative


data Constr (γ : KindCtx) : Set where
  [_==_] : γ ⊢= k₁ → γ ⊢= k₂ → Constr γ
  [_==_+_] : γ ⊢= k₁ → γ ⊢= k₂ → γ ⊢= k₃ → Constr γ

data ⟦_⟧ᶜ¹ : Constr γ → Set where
  ≡⟦_⟧ : {x y : γ ⊢= k}   → x ≔ y     → ⟦ [ x == y ] ⟧ᶜ¹
  +⟦_⟧ : {x y z : γ ⊢= k} → x ≔ y + z → ⟦ [ x == y + z ] ⟧ᶜ¹


⟦_⟧ : List (Constr γ) → Set
⟦_⟧ = All ⟦_⟧ᶜ¹

_<|ᶜ¹_ : (∀ {k} → γ ∋= k → δ ⊢= k) → Constr γ → Constr δ
f <|ᶜ¹ [ x == y ] = [ f <| x == f <| y ]
f <|ᶜ¹ [ x == y + z ] = [ f <| x == f <| y + f <| z ]

<|ᶜ¹-assoc : (σ : ∀ {k} → γ ∋= k → δ ⊢= k) → (θ : ∀ {k} → δ ∋= k → ξ ⊢= k) → ∀ c → (θ <|ᶜ¹ (σ <|ᶜ¹ c)) ≡ ((θ <> σ) <|ᶜ¹ c)
<|ᶜ¹-assoc σ θ [ x == y ] = cong₂ [_==_] (Unificationₚ.<|-assoc θ σ x) (Unificationₚ.<|-assoc θ σ y)
<|ᶜ¹-assoc σ θ [ x == y + z ]
  rewrite Unificationₚ.<|-assoc θ σ x
  | Unificationₚ.<|-assoc θ σ y
  | Unificationₚ.<|-assoc θ σ z
  = refl

_<|ᶜ_ : (∀ {k} → γ ∋= k → δ ⊢= k) → List (Constr γ) → List (Constr δ)
_<|ᶜ_ f = List.map (f <|ᶜ¹_)

<|ᶜ-assoc : (σ : ∀ {k} → γ ∋= k → δ ⊢= k) → (θ : ∀ {k} → δ ∋= k → ξ ⊢= k) → ∀ c → (θ <|ᶜ (σ <|ᶜ c)) ≡ ((θ <> σ) <|ᶜ c)
<|ᶜ-assoc σ θ cs = trans (sym (Listₚ.map-compose cs)) (Listₚ.map-cong (<|ᶜ¹-assoc σ θ) cs)


<|ᵛ-assoc : (f : ∀ {k} → δ ∋= k → ξ ⊢= k) (g : ∀ {k} → γ ∋= k → δ ⊢= k) (Γ : Ctx n γ) → (f <> g) <|ᵛ Γ ≡ f <|ᵛ (g <|ᵛ Γ)
<|ᵛ-assoc f g Γ = trans (sym (Vecₚ.map-cong (Unificationₚ.<|-assoc _ _) _)) (Vecₚ.map-∘ _ _ _)

FreeSubst : KindCtx → KindCtx → Set
FreeSubst γ δ = ∀ {k} → γ ∋= k → δ ⊢= k

-- Indexed soundness and completeness
-- W is the witness or solution
-- P is the premise
-- C is the conclusion
module _ {i w p} {I : Set i} {W : Set w} (P : I → W → Set p) where
  Unsat : W → Set _
  Unsat w = (i : I) → ¬ P i w

  module _ {c} (C : I → Set c) where
    Sound : W → Set _
    Sound w = (i : I) → P i w → C i

    -- For every other solution either the conclusion does not hold, or it implies our solution
    Complete : W → Set _
    Complete w = (w' : W) (i : I) → (P i w' → ¬ C i) ⊎ (P i w' → P i w)

ConstrSubst¹ : ∀ {p} → (FreeSubst γ δ → Set p) → Set p
ConstrSubst¹ P = Σ[ c ∈ Constr _ ] Sound {I = FreeSubst _ _} (λ σ c → ⟦ σ <|ᶜ¹ c ⟧ᶜ¹) P c
syntax ConstrSubst¹ {γ} {δ} (λ σ → P) = ∀⟦ σ ∶ γ ↦ δ ⟧¹ P

ConstrSubst : ∀ {p} → (FreeSubst γ δ → Set p) → Set p
ConstrSubst P = Σ[ c ∈ List (Constr _) ] Sound {I = FreeSubst _ _} (λ σ c → ⟦ σ <|ᶜ c ⟧) P c
syntax ConstrSubst {γ} {δ} (λ σ → P) = ∀⟦ σ ∶ γ ↦ δ ⟧ P

⊢-∶-assoc : (σ₁ : FreeSubst δ θ) (σ₂ : FreeSubst γ δ) {e : Expr n} (t : Type γ)
          → ((σ₁ <> σ₂) <|ᵛ Γ)  ⊢ e ∶ ((σ₁ <> σ₂) <| t)
          → (σ₁ <|ᵛ (σ₂ <|ᵛ Γ)) ⊢ e ∶ (σ₁ <| (σ₂ <| t))
⊢-∶-assoc σ₁ σ₂ t p = p
  |>> subst (λ ● → _ ⊢ _ ∶ ●) (sym (Unificationₚ.<|-assoc σ₁ σ₂ t))
  |>> subst (λ ● → ● ⊢ _ ∶ _) (<|ᵛ-assoc _ _ _)

<< : γ ∋= k → (γ List.++ δ) ∋= k
<< (! zero) = !zero
<< (! suc i) = !suc (<< (! i))

>> : γ ∋= k → (δ List.++ γ) ∋= k
>> {δ = []} i = i
>> {δ = _ ∷ _} i = !suc (>> i)

fresh : Σ[ γ ∈ KindCtx ] Ctx n γ
fresh {zero} = [] , []
fresh {suc n} = Product.map (type ∷_) (λ Γ → (var !zero) ∷ (|> !suc <|ᵛ Γ)) fresh

un-constr¹ : (t : γ ⊢= k) → ∀⟦ σ ∶ γ ↦ δ ⟧¹ (+-un (σ <| t))
un-constr¹ t = [ t == t + t ] , λ {_ +⟦ x ⟧ → x}

un-constr : (Γ : Ctx n γ) → ∀⟦ σ ∶ γ ↦ δ ⟧ (⊎-un (σ <|ᵛ Γ))
un-constr [] = [] , (λ σ x → [])
un-constr (x ∷ xs) =
  let c , p = un-constr¹ x in
  let cs , ps = un-constr xs in
  c ∷ cs , λ { σ (un-x ∷ un-xs) → (p σ un-x) ∷ (ps σ un-xs)}

un-var : (i : Fin n) (Γ : Ctx n γ) → ∀⟦ σ ∶ γ ↦ δ ⟧ ((σ <|ᵛ Γ) ∋ i ∶ (σ <| Vec.lookup Γ i))
un-var zero (x ∷ xs) =
  let cs , ps = un-constr xs in
  cs , λ σ un-xs → _ , zero , ps σ un-xs
un-var {n = suc _} {δ = δ} (suc i) (x ∷ xs@(_ ∷ _)) =
  let c , p = un-constr¹ {δ = δ} x in
  let cs , ps = un-var i xs in
  (c ∷ cs) , λ { σ (+⟦ un-x ⟧ ∷ un-var-xs) →
                 let _ , var-x , un-xs = ps σ un-var-xs in
                 _ , suc var-x , un-x ∷ un-xs}

map-==-+ : Ctx n γ → Ctx n δ → Ctx n θ → List (Constr (γ List.++ (δ List.++ θ)))
map-==-+ [] [] [] = []
map-==-+ {γ = γ} (x ∷ Γ) (y ∷ Δ) (z ∷ Θ) = [ (|> << <| x) == (|> ((>> {δ = γ}) ∘ <<) <| y) + (|> ((>> {δ = γ}) ∘ >>) <| z) ] ∷ map-==-+ Γ Δ Θ

⟦map-==-+⟧ : ∀ {ξ} (Γ : Ctx n γ) (Δ : Ctx n δ) (Θ : Ctx n θ) (σ : FreeSubst (γ List.++ δ List.++ θ) ξ) → ⟦ σ <|ᶜ map-==-+ Γ Δ Θ ⟧
           → (σ <|ᵛ (|> << <|ᵛ Γ)) ≐ (σ <|ᵛ (|> ((>> {δ = γ}) ∘ <<) <|ᵛ Δ)) ⊎ (σ <|ᵛ (|> ((>> {δ = γ}) ∘ >>) <|ᵛ Θ))
⟦map-==-+⟧ [] [] [] σ C = []
⟦map-==-+⟧ (x ∷ Γ) (y ∷ Δ) (z ∷ Θ) σ (+⟦ c ⟧ ∷ C) = c ∷ ⟦map-==-+⟧ Γ Δ Θ σ C

<|ᶜ¹-≗ : {f g : ∀ {k} → γ ∋= k → δ ⊢= k} → Unificationₚ._≗_ {P = γ ∋=_} f g → Unificationₚ._≗_ {A = ⊤} {P = λ _ → Constr γ} (f <|ᶜ¹_) (g <|ᶜ¹_)
<|ᶜ¹-≗ eq [ x == y ] rewrite Unificationₚ.<|-≗ eq x | Unificationₚ.<|-≗ eq y = refl
<|ᶜ¹-≗ eq [ x == y + z ] rewrite Unificationₚ.<|-≗ eq x | Unificationₚ.<|-≗ eq y | Unificationₚ.<|-≗ eq z = refl


module _ where
  private
    variable
      as bs cs : List (Constr γ)
      a b c : Constr γ

  data _⇔_ : List (Constr γ) → List (Constr γ) → Set where
    ⇔-refl : as ⇔ as
    ⇔-skip : as ⇔ bs → (a ∷ as) ⇔ (a ∷ bs)
    ⇔-sym : as ⇔ bs → bs ⇔ as
    ⇔-trans : as ⇔ bs → bs ⇔ cs → as ⇔ cs
    ⇔-swap : (a ∷ b ∷ cs) ⇔ (b ∷ a ∷ cs)
    ⇔-weakening : (a ∷ a ∷ cs) ⇔ (a ∷ cs)
    ⇔-contraction : (a ∷ cs) ⇔ (a ∷ a ∷ cs)

    ⇔-==-usage : {x : Usage γ} → ([ x == x ] ∷ cs) ⇔ cs
    ⇔-==-⊤ : ([ ‵⊤ == ‵⊤ ] ∷ cs) ⇔ cs
    ⇔-==-# : ([ # iₗ oₗ tₗ == # iᵣ oᵣ tᵣ ] ∷ cs)
           ⇔ ([ iₗ == iᵣ ] ∷ [ oₗ == oᵣ ] ∷ [ tₗ == tᵣ ] ∷ cs)
    ⇔-==-× : ([ sₗ ‵× tₗ == sᵣ ‵× tᵣ ] ∷ cs)
           ⇔ ([ sₗ == sᵣ ] ∷ [ tₗ == tᵣ ] ∷ cs)
    ⇔-==-+ : ([ sₗ ‵+ tₗ == sᵣ ‵+ tᵣ ] ∷ cs)
           ⇔ ([ sₗ == sᵣ ] ∷ [ tₗ == tᵣ ] ∷ cs)

    ⇔-=+=-usage : {x y z : Usage γ} → x ≔ y + z → ([ x == y + z ] ∷ cs) ⇔ cs
    ⇔-=+=-⊤ : ([ ‵⊤ == ‵⊤ + ‵⊤ ] ∷ cs) ⇔ cs
    ⇔-=+=-# : ([ # i o t == # iₗ oₗ tₗ + # iᵣ oᵣ tᵣ ] ∷ cs)
            ⇔ ([ i == iₗ + iᵣ ] ∷ [ o == oₗ + oᵣ ] ∷ [ t == tₗ ] ∷ [ tₗ == tᵣ ] ∷ cs)
    ⇔-=+=-× : ([ s ‵× t == sₗ ‵× tₗ + sᵣ ‵× tᵣ ] ∷ cs)
            ⇔ ([ s == sₗ + sᵣ ] ∷ [ t == tₗ + tᵣ ] ∷ cs)
    ⇔-=+=-+ : ([ s ‵+ t == sₗ ‵+ tₗ + sᵣ ‵+ tᵣ ] ∷ cs)
            ⇔ ([ s == sₗ + sᵣ ] ∷ [ t == tₗ + tᵣ ] ∷ cs)

  ⇔-sound : as ⇔ bs → (σ : FreeSubst _ δ) → ⟦ σ <|ᶜ as ⟧ → ⟦ σ <|ᶜ bs ⟧
  ⇔-complete : as ⇔ bs → (σ : FreeSubst _ δ) → ⟦ σ <|ᶜ bs ⟧ → ⟦ σ <|ᶜ as ⟧

  ⇔-sound ⇔-refl σ ps = ps
  ⇔-sound (⇔-skip xs) σ (px ∷ ps) = px ∷ ⇔-sound xs σ ps
  ⇔-sound (⇔-sym xs) σ ps = ⇔-complete xs σ ps
  ⇔-sound (⇔-trans xs ys) σ ps = ⇔-sound ys σ (⇔-sound xs σ ps)
  ⇔-sound ⇔-swap σ (px ∷ py ∷ ps) = py ∷ px ∷ ps
  ⇔-sound ⇔-weakening σ (px ∷ py ∷ ps) = px ∷ ps
  ⇔-sound ⇔-contraction σ (px ∷ ps) = px ∷ px ∷ ps
  ⇔-sound ⇔-==-usage σ (px ∷ ps) = ps
  ⇔-sound ⇔-==-⊤ σ (px ∷ ps) = ps
  ⇔-sound ⇔-==-# σ (≡⟦ chan +i +o ≡t ⟧ ∷ ps) = ≡⟦ +i ⟧ ∷ ≡⟦ +o ⟧ ∷ ≡⟦ ≡t ⟧ ∷ ps
  ⇔-sound ⇔-==-× σ (≡⟦ prod ≡l ≡r ⟧ ∷ ps) = ≡⟦ ≡l ⟧ ∷ ≡⟦ ≡r ⟧ ∷ ps
  ⇔-sound ⇔-==-+ σ (≡⟦ sum ≡l ≡r ⟧ ∷ ps) = ≡⟦ ≡l ⟧ ∷ ≡⟦ ≡r ⟧ ∷ ps
  ⇔-sound (⇔-=+=-usage sp) σ (px ∷ ps) = ps
  ⇔-sound ⇔-=+=-⊤ σ (px ∷ ps) = ps
  ⇔-sound ⇔-=+=-# σ (+⟦ chan +i +o ≡t ≡t' ⟧ ∷ ps) = +⟦ +i ⟧ ∷ +⟦ +o ⟧ ∷ ≡⟦ ≡t ⟧ ∷ ≡⟦ ≡t' ⟧ ∷ ps
  ⇔-sound ⇔-=+=-× σ (+⟦ prod +l +r ⟧ ∷ ps) = +⟦ +l ⟧ ∷ +⟦ +r ⟧ ∷ ps
  ⇔-sound ⇔-=+=-+ σ (+⟦ sum +l +r ⟧ ∷ ps) = +⟦ +l ⟧ ∷ +⟦ +r ⟧ ∷ ps

  ⇔-complete ⇔-refl σ ps = ps
  ⇔-complete (⇔-skip xs) σ (px ∷ ps) = px ∷ ⇔-complete xs σ ps
  ⇔-complete (⇔-sym xs) σ ps = ⇔-sound xs σ ps
  ⇔-complete (⇔-trans xs ys) σ ps = ⇔-complete xs σ (⇔-complete ys σ ps)
  ⇔-complete ⇔-swap σ (px ∷ py ∷ ps) = py ∷ px ∷ ps
  ⇔-complete ⇔-weakening σ (px ∷ ps) = px ∷ px ∷ ps
  ⇔-complete ⇔-contraction σ (px ∷ py ∷ ps) = px ∷ ps
  ⇔-complete ⇔-==-usage σ ps = ≡⟦ usage ⟧ ∷ ps
  ⇔-complete ⇔-==-⊤ σ ps = ≡⟦ top ⟧ ∷ ps
  ⇔-complete ⇔-==-# σ (≡⟦ ≡i ⟧ ∷ ≡⟦ ≡o ⟧ ∷ ≡⟦ ≡t ⟧ ∷ ps) = ≡⟦ chan ≡i ≡o ≡t ⟧ ∷ ps
  ⇔-complete ⇔-==-× σ (≡⟦ ≡l ⟧ ∷ ≡⟦ ≡r ⟧ ∷ ps) = ≡⟦ prod ≡l ≡r ⟧ ∷ ps
  ⇔-complete ⇔-==-+ σ (≡⟦ ≡l ⟧ ∷ ≡⟦ ≡r ⟧ ∷ ps) = ≡⟦ sum ≡l ≡r ⟧ ∷ ps
  ⇔-complete (⇔-=+=-usage left) σ ps = +⟦ left ⟧ ∷ ps
  ⇔-complete (⇔-=+=-usage right) σ ps = +⟦ right ⟧ ∷ ps
  ⇔-complete (⇔-=+=-usage shared) σ ps = +⟦ shared ⟧ ∷ ps
  ⇔-complete ⇔-=+=-⊤ σ ps = +⟦ top ⟧ ∷ ps
  ⇔-complete ⇔-=+=-# σ (+⟦ +i ⟧ ∷ +⟦ +o ⟧ ∷ ≡⟦ ≡t ⟧ ∷ ≡⟦ ≡t' ⟧ ∷ ps) = +⟦ chan +i +o ≡t ≡t' ⟧ ∷ ps
  ⇔-complete ⇔-=+=-× σ (+⟦ +l ⟧ ∷ +⟦ +r ⟧ ∷ ps) = +⟦ prod +l +r ⟧ ∷ ps
  ⇔-complete ⇔-=+=-+ σ (+⟦ +l ⟧ ∷ +⟦ +r ⟧ ∷ ps) = +⟦ sum +l +r ⟧ ∷ ps

  data Normalised : Constr γ → Set where
    var-== : {x : γ ∋= k₁} {t : γ ⊢= k₂} → Normalised [ var x == t ]
    ==-var : {x : γ ∋= k₁} {t : γ ⊢= k₂} → Normalised [ t == var x ]
    var-==-+ : {x : γ ∋= k₁} {s t : γ ⊢= k₂} → Normalised [ var x == s + t ]
    ==-var-+ : {x : γ ∋= k₁} {s t : γ ⊢= k₂} → Normalised [ s == var x + t ]
    ==-+-var : {x : γ ∋= k₁} {s t : γ ⊢= k₂} → Normalised [ s == t + var x ]

  normalise : (as : List (Constr γ)) → ∃[ bs ] as ⇔ bs × (All Normalised bs ⊎ Unsat {I = FreeSubst _ δ} (λ σ c → ⟦ σ <|ᶜ c ⟧) bs)
  normalise [] = [] , ⇔-refl , inj₁ []
  normalise ([ var x == y ] ∷ as)
    with bs , as⇔bs , p ← normalise as
    = [ var x == y ] ∷ bs , ⇔-skip as⇔bs , Sum.map (var-== ∷_) (λ {unsat i (_ ∷ ps) → unsat i ps}) p
  normalise ([ x == var y ] ∷ as)
    with bs , as⇔bs , p ← normalise as
    = [ x == var y ] ∷ bs , ⇔-skip as⇔bs , Sum.map (==-var ∷_) (λ {unsat i (_ ∷ ps) → unsat i ps}) p
  normalise ([ ‵⊤ == ‵⊤ ] ∷ as)
    with bs , as⇔bs , p ← normalise as
    = bs , ⇔-trans ⇔-==-⊤ as⇔bs , p
  normalise ([ # ix ox tx == # iy oy ty ] ∷ as) = {!!}
  normalise ([ sx ‵× tx == sy ‵× ty ] ∷ as) = {!!}
  normalise ([ sx ‵+ tx == sy ‵+ ty ] ∷ as) = {!!}
  normalise ([ x == y ] ∷ as) = {!!}
  normalise ([ x == x₁ + x₂ ] ∷ as) = {!!}

  data Value : Constr γ → Set where
    type-var : {x y z : γ ∋= type} → Value [ var x == var y + var z ]
    usage-var-==-+ : {x : γ ∋= multiplicity} {s t : γ ⊢= multiplicity} → Value [ var x == s + t ]
    usage-==-var-+ : {x : γ ∋= multiplicity} {s t : γ ⊢= multiplicity} → Value [ s == var x + t ]
    usage-==-+-var : {x : γ ∋= multiplicity} {s t : γ ⊢= multiplicity} → Value [ s == t + var x ]

  solve : (as : List (Constr γ)) → All Normalised as → Dec (Σ[ δ ∈ KindCtx ] Σ[ sol ∈ Subst _ δ ] (∀ {ξ} (σ : FreeSubst _ ξ) → ⟦ (σ <> sub sol) <|ᶜ as ⟧))
  solve .[] [] = yes (_ , [] , λ σ → [] )
  solve .([ var _ == _ ] ∷ _) (var-== ∷ nas) = {!!}
  solve .([ _ == var _ ] ∷ _) (==-var ∷ nas) = {!!}
  solve .([ var _ == _ + _ ] ∷ _) (var-==-+ ∷ nas) = {!!}
  solve .([ _ == var _ + _ ] ∷ _) (==-var-+ ∷ nas) = {!!}
  solve .([ _ == _ + var _ ] ∷ _) (==-+-var ∷ nas) = {!!}

constrExpr : (e : Expr n) → Σ[ γ ∈ KindCtx ] Σ[ Γ ∈ Ctx n γ ] Σ[ t ∈ Type γ ] ∀⟦ σ ∶ γ ↦ δ ⟧ ((σ <|ᵛ Γ) ⊢ e ∶ (σ <| t))
constrExpr {n = n} top =
  let γ , Γ = fresh in
  let cs , f = un-constr Γ in
  _ , Γ , ‵⊤ , cs , λ where σ xs → top (f σ xs)
constrExpr {n = suc _} (var i) =
  let γ , Γ = fresh in
  let cs , ps = un-var i Γ in
  _ , Γ , Vec.lookup Γ i , cs , λ σ var-Γ → var (ps σ var-Γ)
constrExpr (fst e) =
  let γ , Γ , t , cs , eP = constrExpr e in
  let +-un-s , sP = un-constr¹ (var (! (suc zero))) in
  let +2 = λ {k} → |> {k = k} (!suc ∘ !suc) in
  type ∷ type ∷ γ
  , +2 <|ᵛ Γ
  , var (! zero)
  , [ +2 <| t == var (! zero) ‵× var (! suc zero) ] ∷ +-un-s ∷ (+2 <|ᶜ cs)
  , λ { σ (≡⟦ t≡0×1 ⟧ ∷ ⟦+-un-s⟧ ∷ xs) →
    fst (sP σ ⟦+-un-s⟧) ((eP (σ <> +2) (subst ⟦_⟧ (<|ᶜ-assoc _ _ _) xs))
                        |>> ⊢-∶-assoc σ +2 t
                        |>> subst (λ ● → (σ <|ᵛ (+2 <|ᵛ Γ)) ⊢ e ∶ ●) {!t≡0×1!})}
constrExpr (snd e) =
  let γ , Γ , t , cs , eP = constrExpr e in
  let +-un-s , sP = un-constr¹ (var (! (suc zero))) in
  let +2 = λ {k} → |> {k = k} (!suc ∘ !suc) in
  type ∷ type ∷ γ
  , +2 <|ᵛ Γ
  , var (! zero)
  , [ +2 <| t == var (! (suc zero)) ‵× var (! zero) ] ∷ +-un-s ∷ (+2 <|ᶜ cs)
  , λ { σ (≡⟦ t≡0×1 ⟧ ∷ ⟦+-un-s⟧ ∷ xs) →
    snd (sP σ ⟦+-un-s⟧) ((eP (σ <> +2) (subst ⟦_⟧ (<|ᶜ-assoc _ _ _) xs))
                        |>> ⊢-∶-assoc σ +2 t
                        |>> subst (λ ● → (σ <|ᵛ (+2 <|ᵛ Γ)) ⊢ e ∶ ●) {!t≡0×1!})}
constrExpr (inl e) =
  let γ , Γ , t , cs , eP = constrExpr e in
  type ∷ γ
  , |> !suc <|ᵛ Γ
  , ((|> !suc <| t) ‵+ var !zero)
  , (|> !suc <|ᶜ cs)
  , λ σ xs → inl (eP (σ <> |> !suc) (subst ⟦_⟧ (<|ᶜ-assoc _ _ _) xs)
                 |>> ⊢-∶-assoc σ (|> !suc) t)
constrExpr (inr e) =
  let γ , Γ , t , cs , eP = constrExpr e in
  type ∷ γ
  , |> !suc <|ᵛ Γ
  , (var !zero ‵+ (|> !suc <| t))
  , (|> !suc <|ᶜ cs)
  , λ σ xs → inr (eP (σ <> |> !suc) (subst ⟦_⟧ (<|ᶜ-assoc _ _ _) xs)
                 |>> ⊢-∶-assoc σ (|> !suc) t)
constrExpr {δ = δ} (l ‵, r) =
  let lγ , lΓ , lt , lcs , lps = constrExpr {δ = δ} l in
  let rγ , rΓ , rt , rcs , rps = constrExpr {δ = δ} r in
  let mγ , mΓ = fresh in
  let congr = map-==-+ mΓ lΓ rΓ in
  let left = (|> (>> {δ = mγ}) ∘ <<) <|ᶜ lcs in
  let right = (|> (>> {δ = mγ}) ∘ >>) <|ᶜ rcs in
  mγ List.++ lγ List.++ rγ
  , |> << <|ᵛ mΓ
  , |> (>> {δ = mγ}) <| ((|> << <| lt) ‵× (|> >> <| rt))
  , congr List.++ (left List.++ right)
  , λ {σ xs →
    let b = subst ⟦_⟧ (Listₚ.map-++-commute (σ <|ᶜ¹_) congr {!!}) xs in
    pair (⟦map-==-+⟧ mΓ lΓ rΓ σ (Allₚ.map⁺ (Allₚ.++⁻ˡ congr (Allₚ.map⁻ xs))))
        (lps (σ <> |> (>> {δ = mγ} ∘ <<)) {!!} |>> {!!})
        {! !}}


constrProc : (p : Proc n) → Σ[ γ ∈ KindCtx ] Σ[ Γ ∈ Ctx n γ ] ∀⟦ σ ∶ γ ↦ δ ⟧ ((σ <|ᵛ Γ) ⊢ p)
constrProc end =
  let γ , Γ = fresh in
  let cs , f = un-constr Γ in
  _ , Γ , cs , λ σ x → end (f σ x)
constrProc (new p)
  with γ , (t ∷ Γ) , cs , f ← constrProc p
  = γ , Γ , cs , λ σ x → new (σ <| t) (f σ x)
constrProc (comp p p₁) = {!!}
constrProc (recv x p) = {!!}
constrProc (send x x₁ p) = {!!}
constrProc (case x p p₁) = {!!}
