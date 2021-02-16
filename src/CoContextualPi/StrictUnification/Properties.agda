open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; _≢_; trans; cong; cong₂; sym; subst; inspect; [_])
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary using (Dec; yes; no)

open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product as Product using (∃; Σ; _×_; ∃-syntax; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Fin.Base as Fin using (Fin; zero; suc)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)

import Data.Nat.Properties as ℕₚ
import Data.Fin.Properties as Finₚ
import Data.Maybe.Properties as Maybeₚ
import Data.Product.Properties as Productₚ
import Data.Vec.Properties as Vecₚ
import Data.List.Properties as Listₚ
import Data.Sum.Properties as Sumₚ

module CoContextualPi.StrictUnification.Properties
  (Kind : Set)                   (decEqKind : ∀          (x y : Kind)     → Dec (x ≡ y))
  (Con : Kind → List Kind → Set) (decEqCon  : ∀ {k} {ks} (x y : Con k ks) → Dec (x ≡ y)) where

open import CoContextualPi.StrictUnification Kind decEqKind Con decEqCon

private
  variable
    n m l : ℕ
    u : Univ
    i : Fin n
    k k' : Kind
    ks ks' γ δ ξ ψ : KindCtx

-- This must be in the stdlib somewhere?
infix 15 _≗_
_≗_ : {A : Set} {P : A → Set} {Q : A → Set} → ({a : A} → P a → Q a) → ({a : A} → P a → Q a) → Set
_≗_ {A = A} {P = P} f g = ∀ {a : A} (x : P a) → f x ≡ g x

<|-id : (t : γ ⊢' u) → var <| t ≡ t
<|-id {u = one _} (var x) = refl
<|-id {u = one _} (con n as) = cong (con n) (<|-id as)
<|-id {u = all _} [] = refl
<|-id {u = all _} (x ∷ xs) = cong₂ _∷_ (<|-id x) (<|-id xs)

<|-assoc : (f : ∀ {k} → δ ∋ k → ξ ⊢ k) (g : ∀ {k} → γ ∋ k → δ ⊢ k) (t : γ ⊢' u) → f <| (g <| t) ≡ (f <> g) <| t
<|-assoc {u = one _} f g (var x) = refl
<|-assoc {u = one _} f g (con n as) = cong (con n) (<|-assoc f g as)
<|-assoc {u = all _} f g [] = refl
<|-assoc {u = all _} f g (x ∷ xs) = cong₂ _∷_ (<|-assoc f g x) (<|-assoc f g xs)

<|-≗ : {f g : ∀ {k} → γ ∋ k → δ ⊢ k} → _≗_ {P = γ ∋_} f g → _≗_ {P = γ ⊢'_} (f <|_) (g <|_)
<|-≗ eq {one _} (var x) = eq x
<|-≗ eq {one _} (con n as) = cong (con n) (<|-≗ eq as)
<|-≗ eq {all _} [] = refl
<|-≗ eq {all _} (x ∷ xs) = cong₂ _∷_ (<|-≗ eq x) (<|-≗ eq xs)

thick-nothing : (x : γ ∋ k ▹ δ) → ∃[ eq ] thick x (_ , x) ≡ inj₂ eq
thick-nothing zero = ! refl
thick-nothing (suc x)
  with ! eq ← thick-nothing x
  rewrite eq = ! refl

thick-reverse : (x : γ ∋ k' ▹ δ) (y : γ ∋ k) {r : δ ∋ k} → thick x y ≡ inj₁ r → ∃[ y' ] (y ≡ thin x y')
thick-reverse zero (! suc y) eq = (! y) , refl
thick-reverse (suc x) (! zero) refl = (! zero) , refl
thick-reverse (suc x) (! suc y) eq
  with inj₁ r ← thick x (! y)
     | [ qe ] ← inspect (thick x) (! y)
  with refl ← eq
  = Product.map (Product.map _ suc) (cong (Product.map _ suc)) (thick-reverse x (! y) qe)

nothing-thick : (x : γ ∋ k ▹ δ) (y : γ ∋ k) → ∀ {eq} → thick x y ≡ inj₂ eq → (! x) ≡ y
nothing-thick zero (! zero) eq = refl
nothing-thick (suc x) (! suc y) _
  with inj₂ r ← thick x (! y)
  | [ qe ] ← inspect (thick x) (! y)
  = cong (Product.map _ suc) (nothing-thick x (! y) qe)

thick-thin : (x : δ ∋ k' ▹ γ) (y : γ ∋ k) → thick x (thin x y) ≡ inj₁ y
thick-thin zero y = refl
thick-thin (suc x) (! zero) = refl
thick-thin (suc x) (! suc y) = cong (Sum.map₁ (Product.map _ suc)) (thick-thin x (! y))

check-thin : (i : δ ∋ k' ▹ γ) (t : δ ⊢' u) {t' : γ ⊢' u}
           → check i t ≡ just t' → t ≡ |> (thin i) <| t'
check-thin {u = one _} i (var x) eq
  with inj₁ y ← thick i x | [ qe ] ← inspect (thick i) x
  with refl ← eq
  with y' , refl ← thick-reverse i x qe
  rewrite thick-thin i y'
  with refl ← qe
  = refl
check-thin {u = one _} i (con n as) eq
  with just y ← check i as | [ qe ] ← inspect (check i) as
  with refl ← eq
  = cong (con n) (check-thin i as qe)
check-thin {u = all _} i [] refl = refl
check-thin {u = all _} i (x ∷ xs) eq
  with just y ← check i x | [ qe ] ← inspect (check i) x
  with just ys ← check i xs | [ qes ] ← inspect (check i) xs
  with refl ← eq
  = cong₂ _∷_ (check-thin i x qe) (check-thin i xs qes)


sub-++ : (xs : Subst δ ξ) (ys : Subst γ δ) → _≗_ {P = γ ∋_} (sub (xs ++ ys)) (sub xs <> sub ys)
sub-++ xs [] t = refl
sub-++ xs (ys -, i ↦ t') {k} t
  rewrite <|-assoc {u = one k} (sub xs) (sub ys) (Sum.[ var , kind-subst t' ] (thick i t))
  = <|-≗ (sub-++ xs ys) (Sum.[ var , kind-subst t' ] (thick i t))


++-id : (xs : Subst γ δ) → [] ++ xs ≡ xs
++-id [] = refl
++-id (xs -, z ↦ r) = cong (_-, z ↦ r) (++-id xs)

++-assoc : (xs : Subst δ ξ) (ys : Subst γ δ) (zs : Subst ψ γ) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc xs ys [] = refl
++-assoc xs ys (zs -, z ↦ r) = cong (_-, z ↦ r) (++-assoc xs ys zs)


flexFlex-sound : (x : δ ∋ k ▹ γ) (y : δ ∋ k) {σ : Subst δ ξ} → flexFlex x y ≡ (! σ) → sub σ (! x) ≡ sub σ y
flexFlex-sound x y eq with thick x y | inspect (thick x) y
flexFlex-sound x y refl | inj₂ _ | [ req ] = cong var (nothing-thick x y req)
flexFlex-sound x y refl | inj₁ z | [ req ]
  with r , refl ← thick-reverse x y req
  with refl , eq ← thick-nothing x
  rewrite eq
  rewrite thick-thin x r = cong var (Sumₚ.inj₁-injective (sym req))

flexRigid-sound : (x : δ ∋ k ▹ γ) (t : δ ⊢ k) {σ : Subst δ ξ}
                  → flexRigid x t ≡ just (! σ) → sub σ (! x) ≡ sub σ <| t
flexRigid-sound x t eq with check x t | inspect (check x) t
flexRigid-sound x t refl | just t' | [ eq ]
  with refl , qe ← thick-nothing x
  rewrite qe | check-thin x t eq = begin
    (var <| t')
      ≡⟨ <|-≗ (λ y → cong Sum.[ var , kind-subst t' ] (sym (thick-thin x y))) t' ⟩
    (Sum.[ var , kind-subst t' ] ∘ thick x ∘ thin x) <| t'
      ≡˘⟨ <|-assoc (Sum.[ var , kind-subst t' ] ∘ thick x) (|> (thin x)) t' ⟩
    (Sum.[ var , kind-subst t' ] ∘ thick x) <| (|> (thin x) <| t')
      ≡⟨ <|-≗ (λ t'' → sym (<|-id _)) (|> (thin x) <| t') ⟩
    (λ y → var <| Sum.[ var , kind-subst t' ] (thick x y)) <| (|> (thin x) <| t')
      ∎
    where open ≡.≡-Reasoning

amgu-step : (eq : List.length γ ≡ suc n) (acc : Subst δ ξ) (z : γ ∋ k ▹ δ) (r : δ ⊢ k) (s t : γ ⊢' u)
          → amgu eq s t (_ , acc -, z ↦ r)
          ≡ Maybe.map (Product.map₂ (_-, z ↦ r))
                      (amgu (dec-length z eq) (r for z <| s) (r for z <| t) (_ , acc))
amgu-step {γ = _ ∷ _} {u = one _} eq acc z r (var x) (var y) = refl
amgu-step {γ = _ ∷ _} {u = one _} eq acc z r (var x) (con ny asy) = refl
amgu-step {γ = _ ∷ _} {u = one _} eq acc z r (con nx asx) (var y) = refl
amgu-step {γ = _ ∷ _} {u = one _} eq acc z r (con {ks = kx} nx asx) (con {ks = ky} ny asy) with Listₚ.≡-dec decEqKind kx ky
amgu-step {γ = _ ∷ _} {u = one _} eq acc z r (con {ks = kx} nx asx) (con {ks = ky} ny asy) | no kx≢ky = refl
amgu-step {γ = _ ∷ _} {u = one _} eq acc z r (con {ks = kx} nx asx) (con {ks = ky} ny asy) | yes refl with decEqCon nx ny
amgu-step {γ = _ ∷ _} {u = one _} eq acc z r (con {ks = kx} nx asx) (con {ks = ky} ny asy) | yes refl | no nx≢ny = refl
amgu-step {γ = _ ∷ _} {u = one _} eq acc z r (con {ks = kx} nx asx) (con {ks = ky} ny asy) | yes refl | yes refl = amgu-step eq acc z r asx asy
amgu-step {γ = _ ∷ _} {u = all _} eq acc z r [] [] = refl
amgu-step {γ = _ ∷ _} {n = n} {u = all _} eq acc z r (x ∷ xs) (y ∷ ys)
    with amgu {n = n} (dec-length z eq) (r for z <| x) (r for z <| y) (_ , acc)
       | inspect (amgu (dec-length z eq) (r for z <| x) (r for z <| y)) (_ , acc)
... | nothing | [ eqacc ] rewrite amgu-step eq acc z r x y rewrite eqacc = refl
... | just (_ , acc') | [ eqacc ]
      with amgu (dec-length z eq) (r for z <| xs) (r for z <| ys) (_ , acc')
        | inspect (amgu (dec-length z eq) (r for z <| xs) (r for z <| ys)) (_ , acc')
...   | nothing | [ eqacc' ] rewrite amgu-step eq acc z r x y | eqacc | amgu-step eq acc' z r xs ys | eqacc' = refl
...   | just (_ , acc'') | [ eqacc' ] rewrite amgu-step eq acc z r x y | eqacc | amgu-step eq acc' z r xs ys | eqacc' = refl


amgu-acc : (eq : List.length γ ≡ n) (s t : γ ⊢' u) (acc : Subst γ ξ) {σ : Subst γ ψ}
         → amgu eq s t (! acc) ≡ just (! σ)
         → ∃[ found ] (σ ≡ found ++ acc)
amgu-acc {u = all _} eq [] [] acc refl = _ , sym (++-id _)
amgu-acc {u = all _} eq (x ∷ xs) (y ∷ ys) acc qe
  with just (_ , acc') ← amgu eq x y (_ , acc)
       | [ xyeq ] ← inspect (amgu eq x y) (_ , acc)
  with just (_ , acc'') ← amgu eq xs ys (_ , acc')
       | [ xsyseq ] ← inspect (amgu eq xs ys) (_ , acc')
  with _ , refl ← amgu-acc eq x y acc xyeq
  with _ , refl ← amgu-acc eq xs ys acc' xsyseq
  with refl ← qe
  = ! sym (++-assoc _ _ acc)
amgu-acc {u = one _} eq (var x) (var y) [] qe = _ , refl
amgu-acc {u = one _} eq (var x) (con ny asy) [] qe = _ , refl
amgu-acc {u = one _} eq (con nx asx) (var y) [] qe = _ , refl
amgu-acc {u = one _} eq (con {kx} nx asx) (con {ky} ny asy) [] qe = _ , refl
amgu-acc {[]} {u = one _} eq s t (acc -, () ↦ r) qe
amgu-acc {n = suc n} {u = one _} eq s t (acc -, z ↦ r) qe
  rewrite amgu-step eq acc z r s t
  with just (_ , acc') ← amgu (dec-length z eq) ((r for z) <| s) ((r for z) <| t) (_ , acc)
       | [ steq ] ← inspect (amgu (dec-length z eq) ((r for z) <| s) ((r for z) <| t)) (_ , acc)
  with refl ← qe
  with ! r ← amgu-acc (dec-length z eq) (r for z <| s) (r for z <| t) acc steq
  = ! cong (_-, _ ↦ _) r


amgu-sound : (eq : List.length γ ≡ n) (s t : γ ⊢' u) (acc : ∃ (Subst γ)) {σ : Subst γ ξ}
           → amgu eq s t acc ≡ just (! σ) → sub σ <| s ≡ sub σ <| t
amgu-sound {u = all _} leq [] [] acc eq = refl
amgu-sound {u = all _} leq (x ∷ xs) (y ∷ ys) (_ , acc) eq
  with just (_ , acc') ← amgu leq x y (_ , acc)
       | [ xyeq ] ← inspect (amgu leq x y) (_ , acc)
  with just (_ , acc'') ← amgu leq xs ys (_ , acc')
       | [ xsyseq ] ← inspect (amgu leq xs ys) (_ , acc')
  with xyf , refl ← amgu-acc leq x y acc xyeq
  with xsysf , refl ← amgu-acc leq xs ys acc' xsyseq
  with refl ← eq
  = cong₂ _∷_ helper (amgu-sound leq xs ys (_ , acc') xsyseq)
  where
    open ≡.≡-Reasoning
    helper : sub (xsysf ++ (xyf ++ acc)) <| x ≡ sub (xsysf ++ (xyf ++ acc)) <| y
    helper = begin
      sub (xsysf ++ (xyf ++ acc)) <| x
        ≡⟨ <|-≗ (sub-++ xsysf (xyf ++ acc)) x ⟩
      ((sub xsysf <|_) ∘ (sub (xyf ++ acc))) <| x
        ≡˘⟨ <|-assoc (sub xsysf) (sub (xyf ++ acc)) x ⟩
      sub xsysf <| ((sub (xyf ++ acc)) <| x)
        ≡⟨ cong (sub xsysf <|_) (amgu-sound leq x y (_ , acc) xyeq) ⟩
      sub xsysf <| ((sub (xyf ++ acc)) <| y)
        ≡⟨ <|-assoc (sub xsysf) (sub (xyf ++ acc)) y ⟩
      ((sub xsysf <|_) ∘ (sub (xyf ++ acc))) <| y
        ≡˘⟨ <|-≗ (sub-++ xsysf (xyf ++ acc)) y ⟩
      sub (xsysf ++ (xyf ++ acc)) <| y
        ∎
amgu-sound {u = one _} leq (var (! x)) (var y) (_ , []) eq = flexFlex-sound x y (Maybeₚ.just-injective eq)
amgu-sound {u = one _} leq (var (! x)) (con ny asy) (_ , []) eq = flexRigid-sound x (con ny asy) eq
amgu-sound {u = one _} leq (con nx asx) (var (! y)) (_ , []) eq = sym (flexRigid-sound y (con nx asx) eq)
amgu-sound {u = one _} leq (con {ks = kx} nx asx) (con {ks = ky} ny asy) (_ , []) eq
  with yes refl ← Listₚ.≡-dec decEqKind kx ky
  with yes refl ← decEqCon nx ny
  = cong (con nx) (amgu-sound leq asx asy idSubst eq)
amgu-sound {γ = []} {u = one _} leq s t (_ , acc -, () ↦ r) eq
amgu-sound {n = suc n} {u = one _} leq s t (_ , acc -, z ↦ r) eq
  rewrite amgu-step leq acc z r s t
  with just (_ , acc') ← amgu (dec-length z leq) (r for z <| s) (r for z <| t) (_ , acc)
       | [ steq ] ← inspect (amgu (dec-length z leq) (r for z <| s) (r for z <| t)) (_ , acc)
  with refl ← eq
  rewrite sym (<|-assoc (sub acc') (Sum.[ var , kind-subst r ] ∘ thick z) s)
  rewrite sym (<|-assoc (sub acc') (Sum.[ var , kind-subst r ] ∘ thick z) t)
  = amgu-sound (dec-length z leq) (r for z <| s) (r for z <| t) (_ , acc) steq


unify-sound : (s t : γ ⊢' u) → Maybe (Σ[ ξ ∈ KindCtx ] Σ[ σ ∈ Subst γ ξ ] sub σ <| s ≡ sub σ <| t)
unify-sound s t with unify s t | inspect (unify s) t
unify-sound s t | nothing | _ = nothing
unify-sound s t | just (_ , σ) | [ eq ] = just (_ , σ , amgu-sound refl s t idSubst eq)
