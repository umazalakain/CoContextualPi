open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym; subst; subst₂; cong-app; cong₂)
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
    k k' : Kind
    γ δ θ ξ : KindCtx
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


data Constr (γ : KindCtx) : Set where
  [_==_] : γ ⊢= k → γ ⊢= k → Constr γ
  [_==_+_] : γ ⊢= k → γ ⊢= k → γ ⊢= k → Constr γ

⟦_⟧ᶜ¹ : Constr γ → Set
⟦_⟧ᶜ¹ [ x == y ] = x ≡ y
⟦_⟧ᶜ¹ [ x == y + z ] = x ≔ y + z

⟦_⟧ : List (Constr γ) → Set
⟦_⟧ = All ⟦_⟧ᶜ¹

_<|ᶜ¹_ : (∀ {k} → γ ∋= k → δ ⊢= k) → Constr γ → Constr δ
f <|ᶜ¹ [ x == y ] = [ f <| x == f <| y ]
f <|ᶜ¹ [ x == y + z ] = [ f <| x == f <| y + f <| z ]

<|ᶜ¹-<> : (σ : ∀ {k} → γ ∋= k → δ ⊢= k) → (θ : ∀ {k} → δ ∋= k → ξ ⊢= k) → ∀ c → (θ <|ᶜ¹ (σ <|ᶜ¹ c)) ≡ ((θ <> σ) <|ᶜ¹ c)
<|ᶜ¹-<> σ θ [ x == y ] = cong₂ [_==_] (Unificationₚ.<|-assoc θ σ x) (Unificationₚ.<|-assoc θ σ y)
<|ᶜ¹-<> σ θ [ x == y + z ]
  rewrite Unificationₚ.<|-assoc θ σ x
  | Unificationₚ.<|-assoc θ σ y
  | Unificationₚ.<|-assoc θ σ z
  = refl

_<|ᶜ_ : (∀ {k} → γ ∋= k → δ ⊢= k) → List (Constr γ) → List (Constr δ)
_<|ᶜ_ f = List.map (f <|ᶜ¹_)

<|ᶜ-<> : (σ : ∀ {k} → γ ∋= k → δ ⊢= k) → (θ : ∀ {k} → δ ∋= k → ξ ⊢= k) → ∀ c → (θ <|ᶜ (σ <|ᶜ c)) ≡ ((θ <> σ) <|ᶜ c)
<|ᶜ-<> σ θ cs = trans (sym (Listₚ.map-compose cs)) (Listₚ.map-cong (<|ᶜ¹-<> σ θ) cs)


infixr 2 !_
pattern !_ t = _ , t


<< : γ ∋= k → (γ List.++ δ) ∋= k
<< (! zero) = !zero
<< (! suc i) = !suc (<< (! i))

>> : γ ∋= k → (δ List.++ γ) ∋= k
>> {δ = []} i = i
>> {δ = _ ∷ _} i = !suc (>> i)

<[_] : γ U⊢= u → (γ List.++ δ) U⊢= u
<[_] = |> << <|_

-- _<|[_] : Subst (n ℕ.+ m) l → UType u n → UType u l
-- _<|[_] σ = (sub σ) <| ∘ <[_]

[_]> : γ U⊢= u → (δ List.++ γ) U⊢= u
[_]> = |> >> <|_

-- [_]|>_ : UType u m → Subst (n ℕ.+ m) l → UType u l
-- [_]|>_ x σ = ((sub σ) <|) [ x ]>



UnboundSubst : ∀ {γ δ} → Set
UnboundSubst {γ} {δ} = ∀ {k} → γ ∋= k → δ ⊢= k

ConstrSubst : ∀ {γ δ p} → (UnboundSubst {γ} {δ} → Set p) → Set p
ConstrSubst P = Σ[ c ∈ List (Constr _) ] ((σ : UnboundSubst) → ⟦ σ <|ᶜ c ⟧ → P σ)
syntax ConstrSubst {γ} {δ} (λ σ → P) = ∀⟦ σ ∶ γ ↦ δ ⟧ P


fresh : Σ[ γ ∈ KindCtx ] Ctx n γ
fresh {zero} = [] , []
fresh {suc n} = Product.map (type ∷_) (λ Γ → (var !zero) ∷ (Vec.map (|> !suc <|_) Γ)) fresh

un-constr : (t : γ ∋= k) → Σ[ c ∈ Constr _ ] ((σ : UnboundSubst {γ} {δ}) → ⟦ σ <|ᶜ¹ c ⟧ᶜ¹ → +-un (σ t))
un-constr (_ , zero) = ([ var (! zero) == var (! zero) + var (! zero) ]) , λ where σ x → x
un-constr (_ , suc i) = let c' , p' = un-constr (! i) in (|> !suc  <|ᶜ¹ c') , (λ where σ x → p' (σ ∘ !suc) (subst ⟦_⟧ᶜ¹ (<|ᶜ¹-<> _ _ _) x))

un-constr' : let γ = List.replicate n type in Σ[ Γ ∈ Ctx n γ ] ∀⟦ σ ∶ γ ↦ δ ⟧ (⊎-un (Vec.map (σ <|_) Γ))
un-constr' {zero} = [] , [] , λ _ _ → []
un-constr' {suc n} =
  let Γ' , cs' , ps = un-constr' {n} in
  let c' , p = un-constr (! zero) in
  var (! zero) ∷ Vec.map (|> !suc <|_) Γ'
  , c' ∷ (|> !suc <|ᶜ cs')
  , λ where σ (x ∷ xs) → p σ x ∷ subst (λ ● → ● ≔ ● ⊎ ●) (trans (Vecₚ.map-cong (sym ∘ (Unificationₚ.<|-assoc σ _)) _) (Vecₚ.map-∘ _ _ _)) (ps (σ <> |> !suc) (subst (All _) (trans (sym (Listₚ.map-compose cs')) (Listₚ.map-cong (<|ᶜ¹-<> _ σ) cs')) xs))

un-var' : let γ = List.replicate (suc n) type in (i : Fin (suc n)) (t : Type γ) → Σ[ Γ ∈ Ctx (suc n) γ ] ∀⟦ σ ∶ γ ↦ δ ⟧ ((Vec.map (σ <|_) Γ) ∋ i ∶ (σ <| t) ′)
un-var' {n = n} i t =
  let Γ , cs , ps = un-constr' {n = suc n} in
  Vec._[_]≔_ Γ i t , cs
  , λ σ x j → (λ {refl → trans (Vecₚ.lookup-map j (_<|_ σ) (Vec._[_]≔_ Γ i t)) (cong (σ <|_) (Vecₚ.lookup∘updateAt i Γ))})
            , (λ {j≢i → subst +-un {!trans (Vecₚ.lookup-map j (_<|_ σ) (Vec._[_]≔_ Γ i t)) {!!}!} {!ps σ x!}})


un-var : let γ = List.replicate (suc n) type in (i : Fin (suc n)) (t : Type γ) → Σ[ Γ ∈ Ctx (suc n) γ ] ∀⟦ σ ∶ γ ↦ δ ⟧ (Σ[ Δ ∈ Ctx n δ ] ((Vec.map (σ <|_) Γ ∋ i ∶ σ <| t ▹ Δ) × ⊎-un Δ))
un-var zero t =
  let Γ , cs , ps = un-constr' in
  t ∷ {!!} , cs , λ σ x → Vec.map (σ <|_) {!!} , zero , {!ps σ x!}
un-var {n = suc _} (suc i) t =
  {!!}

map-==-+ : Ctx n γ → Ctx n δ → Ctx n θ → List (Constr (γ List.++ (δ List.++ θ)))
map-==-+ [] [] [] = []
map-==-+ {γ = γ} (x ∷ Γ) (y ∷ Δ) (z ∷ Θ) = [ <[ x ] == [_]> {δ = γ} <[ y ] + [_]> {δ = γ} [ z ]> ] ∷ map-==-+ Γ Δ Θ

⟦map-==-+⟧ : ∀ {ξ} (Γ : Ctx n γ) (Δ : Ctx n δ) (Θ : Ctx n θ) (σ : UnboundSubst {γ List.++ δ List.++ θ} {ξ}) → ⟦ σ <|ᶜ map-==-+ Γ Δ Θ ⟧
           → Vec.map (_<|_ σ) (Vec.map <[_] Γ) ≔ Vec.map (_<|_ σ) (Vec.map (([_]> {δ = γ}) ∘ <[_]) Δ) ⊎ Vec.map (_<|_ σ) (Vec.map (([_]> {δ = γ}) ∘ [_]>) Θ)
⟦map-==-+⟧ [] [] [] σ C = []
⟦map-==-+⟧ (x ∷ Γ) (y ∷ Δ) (z ∷ Θ) σ (c ∷ C) = c ∷ (⟦map-==-+⟧ Γ Δ Θ σ C)

constrExpr : (e : Expr n) → Σ[ γ ∈ KindCtx ] Σ[ Γ ∈ Ctx n γ ] Σ[ t ∈ Type γ ] ∀⟦ σ ∶ γ ↦ δ ⟧ ((Vec.map (σ <|_) Γ) ⊢ e ∶ (σ <| t))
constrExpr {n = n} top =
  let Γ , cs , f = un-constr' in
  _ , Γ , ‵⊤ , cs , λ where σ xs → top (f σ xs)
constrExpr {n = suc _} (var x) = {!!} , {!!} , {!!} , {!!} , λ σ x₁ → var (! {!!} , {!!})
constrExpr (fst e) =
  let γ' , Γ' , t , cs' , ps' = constrExpr e in
  let +-un-s , p' = un-constr (! (suc zero)) in
  let t' = |> (!suc ∘ !suc) <| t in
  type ∷ type ∷ γ'
  , Vec.map (|> (!suc ∘ !suc) <|_) Γ'
  , var (! zero)
  , [ t' == var (! zero) ‵× var (! suc zero) ] ∷ +-un-s ∷ (|> (!suc ∘ !suc)  <|ᶜ cs')
  , λ where σ xs → let t≡0×1 , xs = All.uncons xs in
                   let ⟦+-un-s⟧ , xs = All.uncons xs in
                   fst (p' σ ⟦+-un-s⟧)
                       (subst (λ ● → ● ⊢ _ ∶ (σ <| (var (! zero) ‵× var (! suc zero)))) (trans (Vecₚ.map-cong (sym ∘ (Unificationₚ.<|-assoc σ _)) _) (Vecₚ.map-∘ _ _ _))
                       (subst (λ ● → Vec.map ((σ <> |> (!suc ∘ !suc)) <|_) Γ' ⊢ e ∶ ●) t≡0×1
                       (subst (λ ● → Vec.map ((σ <> |> (!suc ∘ !suc)) <|_) Γ' ⊢ e ∶ ●) (sym (Unificationₚ.<|-assoc σ (|> (!suc ∘ !suc)) t))
                       (ps' (σ <> |> (!suc ∘ !suc)) (subst (All _) (trans (sym (Listₚ.map-compose _)) (Listₚ.map-cong (<|ᶜ¹-<> _ σ) _)) xs)))))
constrExpr (snd e) = {!!}
constrExpr (inl e) = {!!}
constrExpr (inr e) = {!!}
constrExpr {δ = δ} (l ‵, r) =
  let lγ , lΓ , lt , lcs , lps = constrExpr {δ = δ} l in
  let rγ , rΓ , rt , rcs , rps = constrExpr {δ = δ} r in
  let mγ , mΓ = fresh in
  mγ List.++ lγ List.++ rγ
  , Vec.map <[_] mΓ
  , [_]> {δ = mγ} (<[ lt ] ‵× [ rt ]>)
  , map-==-+ mΓ lΓ rΓ List.++ ((|> (>> {δ = mγ}) ∘ <<) <|ᶜ lcs List.++ (|> ((>> {δ = mγ}) ∘ >>) <|ᶜ rcs))
  , λ where σ xs → pair (⟦map-==-+⟧ mΓ lΓ rΓ σ (Allₚ.map⁺ (Allₚ.++⁻ˡ (map-==-+ mΓ lΓ rΓ) (Allₚ.map⁻ xs)))) {!lps ? ?!} {!!}


constrProc : (p : Proc n) → Σ[ γ ∈ KindCtx ] Σ[ Γ ∈ Ctx n γ ] ∀⟦ σ ∶ γ ↦ δ ⟧ ((Vec.map (σ <|_) Γ) ⊢ p)
constrProc end =
  let Γ , cs , f = un-constr' in
  _ , Γ , cs , λ σ x → end (f σ x)
constrProc (new p)
  with γ , (t ∷ Γ) , cs , f ← constrProc p
  = γ , Γ , cs , λ σ x → new (σ <| t) (f σ x)
constrProc (comp p p₁) = {!!}
constrProc (recv x p) = {!!}
constrProc (send x x₁ p) = {!!}
constrProc (case x p p₁) = {!!}
