
open import Function using (_∘_; _$_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; _≢_; trans; cong; cong₂; sym; inspect; [_])
open import Relation.Nullary using (¬_; Dec; _because_; yes; no; does)
import Relation.Nullary.Decidable as Decidable
open import Relation.Nullary.Negation using (contradiction)
import Level

open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Unit as Unit using (⊤; tt)
open import Data.Empty as Empty using (⊥)
open import Data.Bool.Base as Bool using (Bool; true; false; if_then_else_)
open import Data.Product as Product using (Σ; _×_; ∃-syntax; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.List as List using (List; []; _∷_; [_])
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs as AllPairs using (AllPairs; []; _∷_)

import Data.List.Properties as Listₚ
import Data.Vec.Properties as Vecₚ
import Data.Nat.Properties as ℕₚ
import Data.Fin.Properties as Finₚ
import Data.Maybe.Properties as Maybeₚ
import Data.Product.Properties as Productₚ

open import CoContextualPi.Types
open import CoContextualPi.TypingRules
open import CoContextualPi.Unification
open import CoContextualPi.Unification.Properties
open import CoContextualPi.Inference

module CoContextualPi.Inference.Properties where

private
  variable
    n m l k : ℕ
    P Q : Process n

{-
foldr-map-id : (σs : List Subst) → List.foldr (λ σ → Vec.map [ σ ]ₜ) [] σs ≡ []
foldr-map-id [] = refl
foldr-map-id (σ ∷ σs) rewrite foldr-map-id σs = refl

foldr-map-cons : (σs : List Subst) (x : Type) (xs : Ctx n)
               → List.foldr (λ σ → Vec.map [ σ ]ₜ) (x ∷ xs) σs
               ≡ List.foldr [_]ₜ x σs ∷ Vec.map (λ x → List.foldr [_]ₜ x σs) xs
foldr-map-cons [] x xs rewrite Vecₚ.map-id xs = refl
foldr-map-cons (σ ∷ σs) x xs rewrite foldr-map-cons σs x xs = cong₂ _∷_ refl (sym (Vecₚ.map-∘ [ σ ]ₜ (λ x → List.foldr [_]ₜ x σs) xs))

apply≡apply′ : (σs : List Subst) (xs : Ctx n) → [ σs ]-ctx xs ≡ [ σs ]-ctx′ xs
apply≡apply′ σs [] = foldr-map-id σs
apply≡apply′ σs (x ∷ xs) = foldr-map-cons σs x xs


map-type-subst-∋ : (Γ : Ctx n) (x : Fin n) {t : Type} {σ : Subst}
                 → Γ ∋ x ∶ t
                 → Vec.map [ σ ]ₜ Γ ∋ x ∶ [ σ ]ₜ t
map-type-subst-∋ (_ ∷ _) zero refl = refl
map-type-subst-∋ (_ ∷ Γ) (suc x) refl = map-type-subst-∋ Γ x refl

map-type-subst-⊢ : {Γ : Ctx n} {P : Process n} {σ : Subst}
                 → Γ ⊢ P → Vec.map [ σ ]ₜ Γ ⊢ P
map-type-subst-⊢ end = end
map-type-subst-⊢ (new t ⊢P) = new _ (map-type-subst-⊢ ⊢P)
map-type-subst-⊢ (comp ⊢P ⊢Q) = comp (map-type-subst-⊢ ⊢P) (map-type-subst-⊢ ⊢Q)
map-type-subst-⊢ {Γ = Γ} (recv x ⊢P) = recv (map-type-subst-∋ Γ _ x) (map-type-subst-⊢ ⊢P)
map-type-subst-⊢ {Γ = Γ} (send x y ⊢P) = send (map-type-subst-∋ Γ _ x) (map-type-subst-∋ Γ _ y) (map-type-subst-⊢ ⊢P)
-}

[_]⇓-⊢ : (σ : AList m l) {xs : Ctx n m} {P : Process n} → xs ⊢ P → [ σ ]⇓ xs ⊢ P
[ σ ]⇓-⊢ {[]} ⊢P = {!!}
[ σ ]⇓-⊢ {x ∷ xs} ⊢P = {!!}
{-
[ [] ]-ctx-⊢ ⊢P = ⊢P
[ σ ∷ σs ]-ctx-⊢ ⊢P = map-type-subst-⊢ ([ σs ]-ctx-⊢ ⊢P)
-}

solve-⊢ : {xs : Ctx n m} {ys : Ctx n l} (eqs : Vec (Eq m) k) {P : Process n} → xs ⊢ P → unify-apply eqs xs ≡ just (l , ys) → ys ⊢ P
solve-⊢ eqs ⊢P eq with amgus eqs []
solve-⊢ eqs ⊢P refl | just (_ , σ) = {!!}
-- solve-⊢ eqs ⊢P eq with unify eqs
-- solve-⊢ eqs ⊢P refl | just σs = [ σs ]-ctx-⊢ ⊢P

{-
x≟x : (x : Metavar) → does (x Metavar.≟ x) ≡ true
x≟x Metavar.leaf = refl
x≟x (Metavar.left x) = x≟x x
x≟x (Metavar.right x) = x≟x x

if-then≡else : ∀ {a} {A : Set a} b (x : A) → (if b then x else x) ≡ x
if-then≡else false x = refl
if-then≡else true x = refl


tauto-inv : (x y : Type) → unify (x == y) ≡ tauto → x ≡ y
tauto-inv (′ x) (# y) eq with occurs? x y
tauto-inv (′ x) (# y) () | true because _
tauto-inv (′ x) (# y) () | false because _
tauto-inv top top eq = refl
tauto-inv (# x) (′ y) eq with occurs? y x
tauto-inv (# x) (′ y) () | true because _
tauto-inv (# x) (′ y) () | false because _
tauto-inv (# x) (# y) eq = cong #_ (tauto-inv x y eq)

subst-∉ : ∀ {i : Metavar} x t → ¬ Contains i x → [ [ i ↦ t ] ]ₜ x ≡ x
subst-∉ {i = i} (′ x) t i∉x with i Metavar.≟ x
subst-∉ {i = i} (′ x) t i∉x | yes refl = contradiction in-′ i∉x
subst-∉ {i = i} (′ x) t i∉x | no i≢x = refl
subst-∉ top t i∉x = refl
subst-∉ (# x) t i∉x = cong #_ (subst-∉ x t (i∉x ∘ in-#))

subst-inv : (x y : Type) {σ : Subst}
          → unify (x == y) ≡ subst σ → [ σ ]ₜ x ≡ [ σ ]ₜ y
subst-inv (′ x) (′ y) refl rewrite x≟x x = sym (if-then≡else _ _)
subst-inv (′ x) top refl rewrite x≟x x = refl
subst-inv (′ x) (# y) eq with occurs? x y
subst-inv (′ x) (# y) refl | no x∉y rewrite x≟x x = cong #_ (sym (subst-∉ _ _ x∉y))
subst-inv top (′ x) refl rewrite x≟x x = refl
subst-inv (# x) (′ y) eq with occurs? y x
subst-inv (# x) (′ y) refl | no y∉x rewrite x≟x y = cong #_ (subst-∉ _ _ y∉x)
subst-inv (# x) (# y) eq = cong #_ (subst-inv x y eq)

sum-cons-inv : (s : Unjust ⊎ List Subst) {σ : Subst} {σs : List Subst}
             → Sum.map₂ (σ ∷_) s ≡ inj₂ σs
             → Σ[ σs' ∈ List Subst ] (σs ≡ σ ∷ σs' × s ≡ inj₂ σs')
sum-cons-inv (inj₂ y) refl = _ , refl , refl


subst-cong : ∀ (σ σ' : Subst) (t : Type) → [ σ' ]ₜ ([ [ σ' ]ₛ σ ]ₜ t) ≡ [ σ ]ₜ ([ σ' ]ₜ t)
subst-cong [ i ↦ t₁ ] [ j ↦ t₂ ] (′ x) with i Metavar.≟ j | i Metavar.≟ x
subst-cong [ i ↦ t₁ ] [ j ↦ t₂ ] (′ x) | yes refl | yes refl rewrite x≟x i | x≟x i = {!!}
subst-cong [ i ↦ t₁ ] [ j ↦ t₂ ] (′ x) | yes refl | no i≢x = {!!}
subst-cong [ i ↦ t₁ ] [ j ↦ t₂ ] (′ x) | no i≢j | r = {!!}
subst-cong σ σ' top = refl
subst-cong σ σ' (# t) = cong #_ (subst-cong σ σ' t)

subst-apply : ∀ {σ : Subst} (σs : List Subst) (x y : Type)
            → [ σ ]ₜ x ≡ [ σ ]ₜ y
            → [ σ ]ₜ (List.foldr [_]ₜ x (List.map [ σ ]ₛ σs)) ≡ [ σ ]ₜ (List.foldr [_]ₜ y (List.map [ σ ]ₛ σs))
subst-apply [] x y eq = eq
subst-apply (σ ∷ σs) x y eq = {!subst-apply σs x y eq!}

subst-comm : ∀ (i : Metavar) (tᵢ tⱼ t : Type) (σ : Subst)
           → unify (tᵢ == tⱼ) ≡ subst σ
           → [ [ i ↦ tᵢ ] ]ₜ ([ σ ]ₜ t)
           ≡ [ σ ]ₜ ([ [ i ↦ tᵢ ] ]ₜ t)
subst-comm i tᵢ tⱼ (′ x) [ l ↦ tₗ ] eq with l Metavar.≟ x
subst-comm i tᵢ tⱼ (′ x) [ l ↦ tₗ ] eq | yes refl with i Metavar.≟ x
subst-comm i tᵢ tⱼ (′ x) [ l ↦ tₗ ] eq | yes refl | yes refl = {!!}
subst-comm i tᵢ tⱼ (′ x) [ l ↦ tₗ ] eq | yes refl | no i≢x rewrite x≟x x = {!!}
subst-comm i tᵢ tⱼ (′ x) [ l ↦ tₗ ] eq | no l≢x with i Metavar.≟ x
subst-comm i tᵢ tⱼ (′ x) [ l ↦ tₗ ] eq | no l≢x | yes refl = {!!}
subst-comm i tᵢ tⱼ (′ x) [ l ↦ tₗ ] eq | no l≢x | no i≢x = {!!}
subst-comm i tᵢ tⱼ top σ eq = refl
subst-comm i tᵢ tⱼ (# t) σ eq = cong #_ (subst-comm i tᵢ tⱼ t σ eq)

inv : ∀ {σ : Subst} {σs : List Subst} (eqs : List NormEq) (x y : Type)
    → unify (x == y) ≡ subst σ
    → crunch (List.map [ σ ]ₑ eqs) ≡ inj₂ σs
    → [ σ ]ₜ (List.foldr [_]ₜ x σs) ≡ [ σ ]ₜ (List.foldr [_]ₜ y σs)
inv [] x y qe refl = subst-inv x y qe
inv (tauto ∷ eqs) x y p q = inv eqs x y p q
inv {[ i ↦ tᵢ ]} (subst [ j ↦ tⱼ ] ∷ eqs) x y p q with i Metavar.≟ j
inv {[ i ↦ tᵢ ]} (subst [ j ↦ tⱼ ] ∷ eqs) x y p q | yes refl with unify (tᵢ == tⱼ) | inspect unify (tᵢ == tⱼ)
inv {[ i ↦ tᵢ ]} (subst [ i ↦ tⱼ ] ∷ eqs) x y p q | yes refl | tauto | tᵢtⱼ = inv eqs x y p q
inv {[ i ↦ tᵢ ]} (subst [ i ↦ tⱼ ] ∷ eqs) x y p q | yes refl | subst σ | tᵢtⱼ with crunch (List.map [ [ i ↦ tᵢ ] ]ₑ eqs) | inspect crunch (List.map [ [ i ↦ tᵢ ] ]ₑ eqs)
inv {[ i ↦ tᵢ ]} (subst [ i ↦ tⱼ ] ∷ eqs) x y p refl | yes refl | subst σ' | [ tᵢtⱼ ] | inj₂ σs' | [ crunch≡ ]
  rewrite subst-comm i tᵢ tⱼ (List.foldr [_]ₜ y σs') σ' tᵢtⱼ
  | subst-comm i tᵢ tⱼ (List.foldr [_]ₜ x σs') σ' tᵢtⱼ = cong [ σ' ]ₜ (inv eqs x y p crunch≡)
inv {[ i ↦ tᵢ ]} (subst [ j ↦ tⱼ ] ∷ eqs) x y p q | no i≢j = inv eqs x y p {!!}


merge-apply : ∀ (xs ys : Ctx n) {σs : List Subst}
            → unify (merge xs ys) ≡ just σs
            → [ σs ]-ctx xs ≡ [ σs ]-ctx ys
merge-apply [] [] eq = refl
merge-apply (x ∷ xs) (y ∷ ys) eq = {!!}
merge-apply (x ∷ xs) (y ∷ ys) {σs} eq with unify (x == y) | inspect unify (x == y)
merge-apply (x ∷ xs) (y ∷ ys) {σs} eq | tauto | I[ qe ] = begin
  List.foldr (λ σ → Vec.map [ σ ]ₜ) (x ∷ xs) σs
    ≡⟨ foldr-map-cons σs x xs ⟩
  List.foldr [_]ₜ x σs ∷ Vec.map (λ x → List.foldr [_]ₜ x σs) xs
    ≡⟨ cong₂ _∷_ (cong (λ ● → List.foldr [_]ₜ ● σs) {!tauto-inv _ _ qe!})
                 (trans (sym (apply≡apply′ σs xs))
                        (trans (merge-apply xs ys {!eq!})
                               (apply≡apply′ σs ys))) ⟩
  List.foldr [_]ₜ y σs ∷ Vec.map (λ y → List.foldr [_]ₜ y σs) ys
    ≡⟨ sym (foldr-map-cons σs y ys) ⟩
  List.foldr (λ σ → Vec.map [ σ ]ₜ) (y ∷ ys) σs
    ∎
merge-apply (x ∷ xs) (y ∷ ys) {σs} eq | just σ | I[ qe ] =
  let σs' , σs≡σ∷σs' , c≡inj₂σs' = sum-cons-inv (crunch $ List.map [ σ ]ₑ $ cross-apply $ List.map unify $ merge xs ys) eq in
    begin
  List.foldr (λ σ → Vec.map [ σ ]ₜ) (x ∷ xs) σs
    ≡⟨ cong (List.foldr _ _) σs≡σ∷σs' ⟩
  List.foldr (λ σ → Vec.map [ σ ]ₜ) (x ∷ xs) (σ ∷ σs')
    ≡⟨ foldr-map-cons (σ ∷ σs') x xs ⟩
  List.foldr [_]ₜ x (σ ∷ σs') ∷ Vec.map (λ x → List.foldr [_]ₜ x (σ ∷ σs')) xs
    ≡⟨ cong₂ _∷_ (inv _ x y qe c≡inj₂σs')
                 (trans (sym (apply≡apply′ (σ ∷ σs') xs))
                        (trans (cong (Vec.map [ σ ]ₜ) (merge-apply xs ys {!qe!}))
                               (apply≡apply′ (σ ∷ σs') ys))) ⟩
  List.foldr [_]ₜ y (σ ∷ σs') ∷ Vec.map (λ y → List.foldr [_]ₜ y (σ ∷ σs')) ys
    ≡⟨ sym (foldr-map-cons (σ ∷ σs') y ys) ⟩
  List.foldr (λ σ → Vec.map [ σ ]ₜ) (y ∷ ys) (σ ∷ σs')
    ≡⟨ cong (List.foldr _ _) (sym σs≡σ∷σs') ⟩
  List.foldr (λ σ → Vec.map [ σ ]ₜ) (y ∷ ys) σs
    ∎

solve-merge : (xs ys : Ctx n)
            → unify-apply (merge (all-left xs) (all-right ys)) (all-right ys)
            ≡ unify-apply (merge (all-left xs) (all-right ys)) (all-left xs)
solve-merge xs ys with unify (merge (all-left xs) (all-right ys)) | inspect unify (merge (all-left xs) (all-right ys))
solve-merge xs ys | unjust x | eq = refl
solve-merge xs ys | just σs | I[ eq ] = cong just (sym {!merge-apply (all-left xs) (all-right ys) eq!})
-}

<|-∋ : {x : Fin n} {t : Type m} (f : Fin m → Type l) (xs : Ctx n m)
     → xs ∋ x ∶ t → Vec.map (f <|_) xs ∋ x ∶ (f <| t)
<|-∋ f xs refl = Vecₚ.lookup-map _ (f <|_) xs

<|-⊢ : {xs : Ctx n l} (f : Fin l → Type m) → xs ⊢ P → Vec.map (f <|_) xs ⊢ P
<|-⊢ f end = end
<|-⊢ f (new t ⊢P) = new (f <| t) (<|-⊢ f ⊢P)
<|-⊢ f (comp ⊢P ⊢Q) = comp (<|-⊢ f ⊢P) (<|-⊢ f ⊢Q)
<|-⊢ {xs = xs} f (recv x ⊢P) = recv (<|-∋ f xs x) (<|-⊢ f ⊢P)
<|-⊢ {xs = xs} f (send x y ⊢P) = send (<|-∋ f xs x) (<|-∋ f xs y) (<|-⊢ f ⊢P)

type-infer-comp : {xs : Ctx n l} {ys : Ctx n m} {zs : Ctx n k} {P Q : Process n} → xs ⊢ P → ys ⊢ Q → merge-solve xs ys ≡ just (k , zs) → zs ⊢ comp P Q
type-infer-comp {xs = xs} {ys = ys} ⊢P ⊢Q eq
   = comp {!<|-⊢!} -- {!solve-⊢ (merge xs ys) (<|-⊢ (|> left-inject) ⊢P) eq!}
          (solve-⊢ (merge xs ys) (<|-⊢ (|> right-inject) ⊢Q) (trans {!!} eq))

type-infer-recv : (x : Fin n) {y : Type m} {Γ : Ctx n m} {Γ' : Ctx n l}
                → (y ∷ Γ) ⊢ P
                → unify-apply ((Vec.lookup Γ x , # y) ∷ []) Γ ≡ just (l , Γ')
                → Γ' ⊢ recv x P
type-infer-recv x {y} {Γ} ⊢P eq = {!!}
-- type-infer-recv x {y = y} {Γ = Γ} ⊢P eq with unify (Vec.lookup Γ x == # y ∷ []) | inspect unify (Vec.lookup Γ x == # y ∷ [])
-- type-infer-recv x {y = y} {Γ = Γ} ⊢P refl | just σs | I[ eq ] = recv {!trans (Vecₚ.lookup-map x [ σs ]ₜ Γ) (subst-inv (Vec.lookup Γ x) (# y) eq)!} {!map-type-subst-⊢ ⊢P!}

type-infer-send : (x y : Fin n) {Γ : Ctx n m} {Γ' : Ctx n l}
                → Γ ⊢ P
                → unify-apply ((Vec.lookup Γ x , # Vec.lookup Γ y) ∷ []) Γ ≡ just (l , Γ')
                → Γ' ⊢ send x y P
type-infer-send x y {Γ} ⊢P eq = {!!}
-- type-infer-send x y {Γ = Γ} ⊢P eq with unify (Vec.lookup Γ x == # Vec.lookup Γ y ∷ []) | inspect unify (Vec.lookup Γ x == # Vec.lookup Γ y ∷ [])
-- type-infer-send x y {Γ = Γ} ⊢P refl | just σs | I[ qe ] = {!send (trans (Vecₚ.lookup-map x [ σ ]ₜ Γ) (subst-inv (Vec.lookup Γ x) (# Vec.lookup Γ y) qe))
--                                                                (Vecₚ.lookup-map y [ σ ]ₜ Γ)
--                                                                (map-type-subst-⊢ ⊢P)!}

type-infer : (P : Process n) {Γ : Ctx n l} → infer P ≡ just (l , Γ) → Γ ⊢ P
type-infer end eq = end
type-infer (new P) eq with infer P | inspect infer P
type-infer (new P) refl | just (_ , t ∷ Γ) | [ eq ] = new t (type-infer P eq)
type-infer (comp P Q) eq with infer P | inspect infer P
type-infer (comp P Q) eq | just (_ , ΓP) | [ peq ] with infer Q | inspect infer Q
type-infer (comp P Q) eq | just (_ , ΓP) | [ peq ] | just (_ , ΓQ) | [ qeq ] = type-infer-comp (type-infer P peq) (type-infer Q qeq) eq
type-infer (recv x P) eq with infer P | inspect infer P
type-infer (recv x P) eq | just (_ , y ∷ Γ) | [ qe ] = type-infer-recv x (type-infer P qe) eq
type-infer (send x y P) eq with infer P | inspect infer P
type-infer (send x y P) eq | just Γ | [ qe ] = type-infer-send x y (type-infer P qe) eq
