open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; _≢_; trans; cong; cong₂; sym; subst; inspect; [_])
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary using (Dec; yes; no)

open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product as Product using (∃; Σ; _×_; ∃-syntax; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Fin.Base as Fin using (Fin; zero; suc)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)

import Data.Nat.Properties as ℕₚ
import Data.Fin.Properties as Finₚ
import Data.Maybe.Properties as Maybeₚ
import Data.Product.Properties as Productₚ
import Data.Vec.Properties as Vecₚ

module CoContextualPi.Unification.Properties (Name : ℕ → Set) (decEqName : ∀ {k} (x y : Name k) → Dec (x ≡ y)) where

open import CoContextualPi.Unification Name decEqName

private
  variable
    n m l k : ℕ
    u : Univ

-- This must be in the stdlib somewhere?
infix 15 _≗_
_≗_ : {A : Set} {B : Set} → (A → B) → (A → B) → Set
f ≗ g = ∀ x → f x ≡ g x

<|-id : (t : UTerm u n) → (var <|) t ≡ t
<|-id {u = one} (var x) = refl
<|-id {u = one} (con n as) = cong (con n) (<|-id as)
<|-id {u = vec _} [] = refl
<|-id {u = vec _} (x ∷ xs) = cong₂ _∷_ (<|-id x) (<|-id xs)

<|-assoc : (f : Fin m → Term n) (g : Fin l → Term m) (t : UTerm u l) → (f <|) ((g <|) t) ≡ ((f <> g) <|) t
<|-assoc {u = one} f g (var x) = refl
<|-assoc {u = one} f g (con n as) = cong (con n) (<|-assoc f g as)
<|-assoc {u = vec _} f g [] = refl
<|-assoc {u = vec _} f g (x ∷ xs) = cong₂ _∷_ (<|-assoc f g x) (<|-assoc f g xs)

<|-≗ : {f g : Fin n → Term m} → f ≗ g → (_<| {u = u} f) ≗ (_<| {u = u} g)
<|-≗ {u = one} eq (var x) = eq x
<|-≗ {u = one} eq (con n as) = cong (con n) (<|-≗ eq as)
<|-≗ {u = vec _} eq [] = refl
<|-≗ {u = vec _} eq (x ∷ xs) = cong₂ _∷_ (<|-≗ eq x) (<|-≗ eq xs)

thick-nothing : (x : Fin (suc n)) → thick x x ≡ nothing
thick-nothing zero = refl
thick-nothing {suc n} (suc x) rewrite thick-nothing x = refl

thick-reverse : ∀ (x y : Fin (suc n)) {r : Fin n} → thick x y ≡ just r → ∃[ y' ] (y ≡ thin x y')
thick-reverse zero (suc y) eq = y , refl
thick-reverse {suc n} (suc x) zero refl = zero , refl
thick-reverse {suc n} (suc x) (suc y) {zero} eq with thick x y
thick-reverse {suc n} (suc x) (suc y) {zero} () | nothing
thick-reverse {suc n} (suc x) (suc y) {zero} () | just _
thick-reverse {suc n} (suc x) (suc y) {suc r} eq =
  Product.map suc (cong suc) (thick-reverse x y (Maybeₚ.map-injective Finₚ.suc-injective eq))

nothing-thick : (x y : Fin (suc n)) → thick x y ≡ nothing → x ≡ y
nothing-thick zero zero eq = refl
nothing-thick {suc n} (suc x) (suc y) eq =
  cong suc (nothing-thick x y (Maybeₚ.map-injective Finₚ.suc-injective eq))

thick-thin : (x : Fin (suc n)) (y : Fin n) → thick x (thin x y) ≡ just y
thick-thin zero y = refl
thick-thin (suc x) zero = refl
thick-thin (suc x) (suc y) = cong (Maybe.map suc) (thick-thin x y)

check-thin : (i : Fin (suc n)) (t : UTerm u (suc n)) {t' : UTerm u n}
           → check i t ≡ just t' → t ≡ (|> (thin i) <|) t'
check-thin {u = one} i (var x) eq
  with just y ← thick i x | [ qe ] ← inspect (thick i) x
  with refl ← eq
  with y' , refl ← thick-reverse i x qe
  rewrite thick-thin i y'
  with refl ← qe
  = refl
check-thin {u = one} i (con n as) eq
  with just y ← check i as | [ qe ] ← inspect (check i) as
  with refl ← eq
  = cong (con n) (check-thin i as qe)
check-thin {u = vec _} i [] refl = refl
check-thin {u = vec _} i (x ∷ xs) eq
  with just y ← check i x | [ qe ] ← inspect (check i) x
  with just ys ← check i xs | [ qes ] ← inspect (check i) xs
  with refl ← eq
  = cong₂ _∷_ (check-thin i x qe) (check-thin i xs qes)


sub-++ : (xs : Subst m n) (ys : Subst l m) → sub (xs ++ ys) ≗ sub xs <> sub ys
sub-++ xs [] t = refl
sub-++ xs (ys -, i ↦ t') t
  rewrite <|-assoc {u = one} (sub xs) (sub ys) (Maybe.maybe var t' (thick i t))
  = <|-≗ (sub-++ xs ys) (Maybe.maybe var t' (thick i t))

++-id : (xs : Subst m n) → [] ++ xs ≡ xs
++-id [] = refl
++-id (xs -, z ↦ r) = cong (_-, z ↦ r) (++-id xs)

++-assoc : (xs : Subst m n) (ys : Subst l m) (zs : Subst k l) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc xs ys [] = refl
++-assoc xs ys (zs -, z ↦ r) = cong (_-, z ↦ r) (++-assoc xs ys zs)


flexFlex-sound : (x y : Fin m) {σ : Subst m n} → flexFlex x y ≡ (n , σ) → sub σ x ≡ sub σ y
flexFlex-sound {suc m} x y eq with thick x y | inspect (thick x) y
flexFlex-sound {suc m} x y refl | nothing | [ req ] = cong var (nothing-thick x y req)
flexFlex-sound {suc m} x y refl | just z | [ req ]
  with r , refl ← thick-reverse x y req
  rewrite thick-nothing x | thick-thin x r = cong var (sym (Maybeₚ.just-injective req))

flexRigid-sound : (x : Fin m) (t : Term m) {σ : Subst m n}
                  → flexRigid x t ≡ just (n , σ) → sub σ x ≡ (sub σ <|) t
flexRigid-sound {suc m} x t eq with check x t | inspect (check x) t
flexRigid-sound {suc m} x t refl | just t' | [ eq ]
  rewrite thick-nothing x | check-thin x t eq = begin
    ((var <|) t')
      ≡⟨ <|-≗ (λ y → cong (Maybe.maybe var t') (sym (thick-thin x y))) t' ⟩
    ((Maybe.maybe var t' ∘ thick x ∘ thin x) <|) t'
      ≡˘⟨ <|-assoc (Maybe.maybe var t' ∘ thick x) (|> (thin x)) t' ⟩
    ((Maybe.maybe var t' ∘ thick x) <|) ((|> (thin x) <|) t')
      ≡⟨ <|-≗ (λ t'' → sym (<|-id _)) ((|> (thin x) <|) t') ⟩
    (((var <|) ∘ Maybe.maybe var t' ∘ thick x) <|) ((|> (thin x) <|) t')
      ∎
    where open ≡.≡-Reasoning

amgu-step : (acc : Subst m n) (z : Fin (suc m)) (r : Term m) (s t : UTerm u (suc m))
          → amgu s t (_ , acc -, z ↦ r)
          ≡ Maybe.map (Product.map₂ (_-, z ↦ r)) (amgu ((r for z <|) s) ((r for z <|) t) (_ , acc))
amgu-step {u = one} acc z r (var x) (var y) = refl
amgu-step {u = one} acc z r (var x) (con ny asy) = refl
amgu-step {u = one} acc z r (con nx asx) (var y) = refl
amgu-step {u = one} acc z r (con {kx} nx asx) (con {ky} ny asy) with kx ℕₚ.≟ ky
amgu-step {u = one} acc z r (con {kx} nx asx) (con {ky} ny asy) | no kx≢ky = refl
amgu-step {u = one} acc z r (con {kx} nx asx) (con {ky} ny asy) | yes refl with decEqName nx ny
amgu-step {u = one} acc z r (con {kx} nx asx) (con {ky} ny asy) | yes refl | no nx≢ny = refl
amgu-step {u = one} acc z r (con {kx} nx asx) (con {ky} ny asy) | yes refl | yes refl = amgu-step acc z r asx asy
amgu-step {u = vec _} acc z r [] [] = refl
amgu-step {u = vec _} acc z r (x ∷ xs) (y ∷ ys)
    with amgu ((r for z <|) x) ((r for z <|) y) (_ , acc)
       | inspect (amgu ((r for z <|) x) ((r for z <|) y)) (_ , acc)
... | nothing | [ eq ] rewrite amgu-step acc z r x y | eq = refl
... | just (_ , acc') | [ eq ]
      with amgu ((r for z <|) xs) ((r for z <|) ys) (_ , acc')
        | inspect (amgu ((r for z <|) xs) ((r for z <|) ys)) (_ , acc')
...   | nothing | [ qe ] rewrite amgu-step acc z r x y | eq | amgu-step acc' z r xs ys | qe = refl
...   | just (_ , acc'') | [ qe ] rewrite amgu-step acc z r x y | eq | amgu-step acc' z r xs ys | qe = refl


amgu-acc : (s t : UTerm u m) (acc : Subst m n) {σ : Subst m l}
         → amgu s t (_ , acc) ≡ just (l , σ)
         → ∃[ found ] (σ ≡ found ++ acc)
amgu-acc {vec _} [] [] acc refl = _ , sym (++-id _)
amgu-acc {vec _} (x ∷ xs) (y ∷ ys) acc eq
  with just (_ , acc') ← amgu x y (_ , acc)
       | [ xyeq ] ← inspect (amgu x y) (_ , acc)
  with just (_ , acc'') ← amgu xs ys (_ , acc')
       | [ xsyseq ] ← inspect (amgu xs ys) (_ , acc')
  with _ , refl ← amgu-acc x y acc xyeq
  with _ , refl ← amgu-acc xs ys acc' xsyseq
  with refl ← eq
  = _ , sym (++-assoc _ _ acc)
amgu-acc {one} (var x) (var y) [] eq = _ , refl
amgu-acc {one} (var x) (con ny asy) [] eq = _ , refl
amgu-acc {one} (con nx asx) (var y) [] eq = _ , refl
amgu-acc {one} (con {kx} nx asx) (con {ky} ny asy) [] eq = _ , refl
amgu-acc {one} s t (acc -, z ↦ r) eq
  rewrite amgu-step acc z r s t
  with just (_ , acc') ← amgu ((r for z <|) s) ((r for z <|) t) (_ , acc)
       | [ steq ] ← inspect (amgu ((r for z <|) s) ((r for z <|) t)) (_ , acc)
  with refl ← eq
  with _ , refl ← amgu-acc ((r for z <|) s) ((r for z <|) t) acc steq
  = _ , refl


amgu-sound : (s t : UTerm u m) (acc : ∃ (Subst m)) {σ : Subst m l}
           → amgu s t acc ≡ just (l , σ) → (sub σ <|) s ≡ (sub σ <|) t
amgu-sound {vec _} [] [] acc eq = refl
amgu-sound {vec _} (x ∷ xs) (y ∷ ys) (_ , acc) eq
  with just (_ , acc') ← amgu x y (_ , acc)
       | [ xyeq ] ← inspect (amgu x y) (_ , acc)
  with just (_ , acc'') ← amgu xs ys (_ , acc')
       | [ xsyseq ] ← inspect (amgu xs ys) (_ , acc')
  with xyf , refl ← amgu-acc x y acc xyeq
  with xsysf , refl ← amgu-acc xs ys acc' xsyseq
  with refl ← eq
  = cong₂ _∷_ helper (amgu-sound xs ys (_ , acc') xsyseq)
  where
    open ≡.≡-Reasoning
    helper : (sub (xsysf ++ (xyf ++ acc)) <|) x ≡ (sub (xsysf ++ (xyf ++ acc)) <|) y
    helper = begin
      (sub (xsysf ++ (xyf ++ acc)) <|) x
        ≡⟨ <|-≗ (sub-++ xsysf (xyf ++ acc)) x ⟩
      (((sub xsysf <|) ∘ (sub (xyf ++ acc))) <|) x
        ≡˘⟨ <|-assoc (sub xsysf) (sub (xyf ++ acc)) x ⟩
      (sub xsysf <|) (((sub (xyf ++ acc)) <|) x)
        ≡⟨ cong (sub xsysf <|) (amgu-sound x y (_ , acc) xyeq) ⟩
      (sub xsysf <|) (((sub (xyf ++ acc)) <|) y)
        ≡⟨ <|-assoc (sub xsysf) (sub (xyf ++ acc)) y ⟩
      (((sub xsysf <|) ∘ (sub (xyf ++ acc))) <|) y
        ≡˘⟨ <|-≗ (sub-++ xsysf (xyf ++ acc)) y ⟩
      (sub (xsysf ++ (xyf ++ acc)) <|) y
        ∎

amgu-sound {one} (var x) (var y) (_ , []) eq = flexFlex-sound x y (Maybeₚ.just-injective eq)
amgu-sound {one} (var x) (con ny asy) (_ , []) eq = flexRigid-sound x (con ny asy) eq
amgu-sound {one} (con nx asx) (var y) (_ , []) eq = sym (flexRigid-sound y (con nx asx) eq)
amgu-sound {one} (con {kx} nx asx) (con {ky} ny asy) (_ , []) eq
  with yes refl ← kx ℕₚ.≟ ky
  with yes refl ← decEqName nx ny
  = cong (con nx) (amgu-sound asx asy idSubst eq)
amgu-sound {one} s t (_ , acc -, z ↦ r) eq
  rewrite amgu-step acc z r s t
  with just (_ , acc') ← amgu ((r for z <|) s) ((r for z <|) t) (_ , acc)
       | [ steq ] ← inspect (amgu ((r for z <|) s) ((r for z <|) t)) (_ , acc)
  with refl ← eq
  rewrite sym (<|-assoc (sub acc') (Maybe.maybe var r ∘ thick z) s)
  rewrite sym (<|-assoc (sub acc') (Maybe.maybe var r ∘ thick z) t)
  = amgu-sound ((r for z <|) s) ((r for z <|) t) (_ , acc) steq


unify-sound : (s t : UTerm u m) → Maybe (Σ[ l ∈ ℕ ] Σ[ σ ∈ Subst m l ] (sub σ <|) s ≡ (sub σ <|) t)
unify-sound s t with unify s t | inspect (unify s) t
unify-sound s t | nothing | _ = nothing
unify-sound s t | just (_ , σ) | [ eq ] = just (_ , σ , amgu-sound s t idSubst eq)
