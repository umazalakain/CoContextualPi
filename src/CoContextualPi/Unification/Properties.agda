open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; _≢_; trans; cong; cong₂; sym; inspect; [_])
open import Relation.Nullary.Negation using (contradiction)

open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product as Product using (Σ; _×_; ∃-syntax; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin; zero; suc)

import Data.Fin.Properties as Finₚ
import Data.Maybe.Properties as Maybeₚ
import Data.Product.Properties as Productₚ

open import CoContextualPi.Types
open import CoContextualPi.Unification

module CoContextualPi.Unification.Properties where

private
  variable
    n m l k : ℕ

<|-id : (t : Type n) → ′_ <| t ≡ t
<|-id (′ x) = refl
<|-id top = refl
<|-id (# t) = cong #_ (<|-id t)
<|-id < t₁ , t₂ > = cong₂ <_,_> (<|-id t₁) (<|-id t₂)

<|-assoc : (f : Fin m → Type n) (g : Fin l → Type m) (t : Type l) → (f <> g) <| t ≡ f <| (g <| t)
<|-assoc f g (′ x) = refl
<|-assoc f g top = refl
<|-assoc f g (# t) = cong #_ (<|-assoc f g t)
<|-assoc f g < t₁ , t₂ > = cong₂ <_,_> (<|-assoc f g t₁) (<|-assoc f g t₂)

<|-≗ : {f g : Fin n → Type m} (t : Type n) → f ≗ g → f <| t ≡ g <| t
<|-≗ (′ x) eq = eq x
<|-≗ top eq = refl
<|-≗ (# t) eq = cong #_ (<|-≗ t eq)
<|-≗ < l , r > eq = cong₂ <_,_> (<|-≗ l eq) (<|-≗ r eq)

thin-inv : (x : Fin (suc n)) (y z : Fin n) → thin x y ≡ thin x z → y ≡ z
thin-inv zero y z eq = Finₚ.suc-injective eq
thin-inv (suc x) zero zero eq = refl
thin-inv (suc x) (suc y) (suc z) eq = cong suc (thin-inv x y z (Finₚ.suc-injective eq))

thin-≢ : (x : Fin (suc n)) (y : Fin n) → thin x y ≢ x
thin-≢ (suc x) (suc y) eq = thin-≢ x y (Finₚ.suc-injective eq)

thin-comp : (x y : Fin (suc n)) → x ≢ y → ∃[ y' ] (thin x y' ≡ y)
thin-comp zero zero x≢y = contradiction refl x≢y
thin-comp zero (suc y) x≢y = y , refl
thin-comp {suc n} (suc x) zero x≢y = zero , refl
thin-comp {suc n} (suc x) (suc y) x≢y = Product.map suc (cong suc) (thin-comp x y (x≢y ∘ cong suc))

thick-nothing : (x : Fin (suc n)) → thick x x ≡ nothing
thick-nothing zero = refl
thick-nothing {suc n} (suc x) rewrite thick-nothing x = refl

thick-thin-yes : ∀ (x y : Fin (suc n)) {r : Fin n} → thick x y ≡ just r → ∃[ y' ] (y ≡ thin x y')
thick-thin-yes zero (suc y) eq = y , refl
thick-thin-yes {suc n} (suc x) zero refl = zero , refl
thick-thin-yes {suc n} (suc x) (suc y) {zero} eq with thick x y
thick-thin-yes {suc n} (suc x) (suc y) {zero} () | nothing
thick-thin-yes {suc n} (suc x) (suc y) {zero} () | just _
thick-thin-yes {suc n} (suc x) (suc y) {suc r} eq =
  Product.map suc (cong suc) (thick-thin-yes x y (Maybeₚ.map-injective Finₚ.suc-injective eq))

thick-thin-no : ∀ (x y : Fin (suc n)) → thick x y ≡ nothing → x ≡ y
thick-thin-no zero zero eq = refl
thick-thin-no {suc n} (suc x) (suc y) eq =
  cong suc (thick-thin-no x y (Maybeₚ.map-injective Finₚ.suc-injective eq))

thick-thin : (x : Fin (suc n)) (y : Fin n) → thick x (thin x y) ≡ just y
thick-thin zero y = refl
thick-thin (suc x) zero = refl
thick-thin (suc x) (suc y) = cong (Maybe.map suc) (thick-thin x y)

for-thin : {t : Type n} (x : Fin (suc n)) → (t for x ∘ thin x) ≗ ′_
for-thin x y = cong (Maybe.maybe ′_ _) (thick-thin x y)

check-thin : (i : Fin (suc n)) (t : Type (suc n)) (t' : Type n) → check i t ≡ just t'
           → t ≡ |> (thin i) <| t'
check-thin i (′ x) t' eq with thick i x | inspect (thick i) x
check-thin i (′ x) .(′ y) refl | just y | [ eq ] with thick-thin-yes i x eq
check-thin i (′ .(thin i y')) .(′ y) refl | just y | [ eq ] | y' , refl
  rewrite thick-thin i y' = cong (′_ ∘ thin i) (Maybeₚ.just-injective eq)
check-thin i top .top refl = refl
check-thin i (# t) t' eq with check i t | inspect (check i) t
check-thin i (# t) .(# t') refl | just t' | [ eq ] = cong #_ (check-thin i t t' eq)
check-thin i < l , r > t' eq with check i l | inspect (check i) l | check i r | inspect (check i) r
check-thin i < l , r > .(< l' , r' >) refl | just l' | [ eql ] | just r' | [ eqr ] =
  cong₂ <_,_> (check-thin i l l' eql) (check-thin i r r' eqr)

sub-++ : (xs : AList m n) (ys : AList l m) → sub (xs ++ ys) ≗ sub xs <> sub ys
sub-++ xs [] t = refl
sub-++ xs (ys -, (i ↦ t')) t
  rewrite sym (<|-assoc (sub xs) (sub ys) (Maybe.maybe ′_ t' (thick i t)))
  = <|-≗ (Maybe.maybe ′_ t' (thick i t)) (sub-++ xs ys)

++-id : (xs : AList m n) → [] ++ xs ≡ xs
++-id [] = refl
++-id (xs -, x) = cong (_-, x) (++-id xs)

++-assoc : (xs : AList m n) (ys : AList l m) (zs : AList k l) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
++-assoc xs ys [] = refl
++-assoc xs ys (zs -, x) = cong (_-, x) (++-assoc xs ys zs)

flexFlex-unifies : (x y : Fin m) (σ : AList m n) → flexFlex x y ≡ (n , σ) → sub σ x ≡ sub σ y
flexFlex-unifies {suc m} x y σ eq with thick x y | inspect (thick x) y
flexFlex-unifies {suc m} x y ._ refl | nothing | [ req ] = cong ′_ (thick-thin-no x y req)
flexFlex-unifies {suc m} x y ._ refl | just z | [ req ] with thick-thin-yes x y req
flexFlex-unifies {suc m} x ._ ._ refl | just z | [ req ] | r , refl
  rewrite thick-nothing x | thick-thin x r = cong ′_ (sym (Maybeₚ.just-injective req))

flexRigid-unifies : (x : Fin m) (t : Type m) {σ : AList m n}
                  → flexRigid x t ≡ just (n , σ) → sub σ x ≡ sub σ <| t
flexRigid-unifies {suc m} x t eq with check x t | inspect (check x) t
flexRigid-unifies {suc m} x t refl | just t' | [ eq ]
  rewrite thick-nothing x | check-thin x t t' eq = begin
    (′_ <| t')
      ≡⟨ <|-≗ t' (λ y → cong (Maybe.maybe ′_ t') (sym (thick-thin x y))) ⟩
    (Maybe.maybe ′_ t' ∘ thick x ∘ thin x) <| t'
      ≡⟨ <|-assoc (Maybe.maybe ′_ t' ∘ thick x) (|> (thin x)) t' ⟩
    (Maybe.maybe ′_ t' ∘ thick x) <| (|> (thin x) <| t')
      ≡⟨ <|-≗ (|> (thin x) <| t') (λ t'' → sym (<|-id _)) ⟩
    ((′_ <|_) ∘ Maybe.maybe ′_ t' ∘ thick x) <| (|> (thin x) <| t')
      ∎
    where open ≡.≡-Reasoning

amgu-step : (acc : AList m n) (z : Fin (suc m)) (r : Type m) (s t : Type (suc m))
          → amgu s t (acc -, (z ↦ r))
          ≡ Maybe.map (Product.map₂ (_-, (z ↦ r)))
                      (amgu (r for z <| s) (r for z <| t) acc)
amgu-step acc z r (′ x) (′ x₁) = refl
amgu-step acc z r (′ x) top = refl
amgu-step acc z r (′ x) (# t) = refl
amgu-step acc z r (′ x) < t , t₁ > = refl
amgu-step acc z r top (′ x) = refl
amgu-step acc z r top top = refl
amgu-step acc z r top (# t) = refl
amgu-step acc z r top < t , t₁ > = refl
amgu-step acc z r (# s) (′ x) = refl
amgu-step acc z r (# s) top = refl
amgu-step acc z r (# s) (# t) = amgu-step acc z r s t
amgu-step acc z r (# s) < t , t₁ > = refl
amgu-step acc z r < s , s₁ > (′ x) = refl
amgu-step acc z r < s , s₁ > top = refl
amgu-step acc z r < s , s₁ > (# t) = refl
amgu-step acc z r < lx , rx > < ly , ry > with amgu (r for z <| lx) (r for z <| ly) acc | inspect (amgu (r for z <| lx) (r for z <| ly)) acc
... | nothing | [ lres ] rewrite amgu-step acc z r lx ly | lres = refl
... | just (_ , acc') | [ lres ] with amgu (r for z <| rx) (r for z <| ry) acc' | inspect (amgu (r for z <| rx) (r for z <| ry)) acc'
... | nothing | [ rres ] rewrite amgu-step acc z r lx ly | lres | amgu-step acc' z r rx ry | rres = refl
... | just x | [ rres ] rewrite amgu-step acc z r lx ly | lres | amgu-step acc' z r rx ry | rres = refl

amgu-acc : (s t : Type m) (acc : AList m n) (σ : AList m l)
         → amgu s t acc ≡ just (l , σ)
         → ∃[ found ] (σ ≡ found ++ acc)
amgu-acc top top acc .acc refl = [] , sym (++-id acc)
amgu-acc (# s) (# t) acc σ eq = amgu-acc s t acc σ eq
amgu-acc < lx , rx > < ly , ry > acc σ eq with amgu lx ly acc | inspect (amgu lx ly) acc
... | just (_ , lσ) | [ req ] with amgu-acc lx ly acc lσ req
... | lfound , refl with amgu-acc rx ry (lfound ++ acc) σ eq
... | rfound , refl = _ , ++-assoc rfound lfound acc
amgu-acc (′ x) (′ y) [] σ eq = _ , refl
amgu-acc (′ x) t [] σ eq = _ , refl
amgu-acc s (′ y) [] σ eq = _ , refl
amgu-acc s t (acc -, z ↦ r) σ eq with amgu s t (acc -, z ↦ r) | amgu-step acc z r s t
amgu-acc s t (acc -, (z ↦ r)) σ refl | just ._ | req with amgu (r for z <| s) (r for z <| t) acc | inspect (amgu (r for z <| s) (r for z <| t)) acc
amgu-acc s t (acc -, (z ↦ r)) ._ refl | just ._ | refl | just x | [ req ] = Product.map₂ (cong (_-, z ↦ r)) (amgu-acc (r for z <| s) (r for z <| t) acc _ req)

amgu-unifies : (s t : Type m) (acc : AList m n) (σ : AList m l)
             → amgu s t acc ≡ just (l , σ) → sub σ <| s ≡ sub σ <| t
amgu-unifies top top acc σ eq = refl
amgu-unifies (# s) (# t) acc σ eq = cong #_ (amgu-unifies s t acc σ eq)
-- FIXME: factor out
amgu-unifies < lx , rx > < ly , ry > acc σ eq with amgu lx ly acc | inspect (amgu lx ly) acc
... | just (_ , lσ) | [ req ] with amgu-acc lx ly acc lσ req
... | lfound , refl with amgu-acc rx ry (lfound ++ acc) σ eq
... | rfound , refl = cong₂ <_,_>
  (begin
     (sub (rfound ++ (lfound ++ acc)) <| lx)
   ≡⟨ <|-≗ lx (sub-++ rfound (lfound ++ acc)) ⟩
     (sub rfound <> sub (lfound ++ acc)) <| lx
   ≡⟨ <|-assoc (sub rfound) (sub (lfound ++ acc)) lx ⟩
     sub rfound <| (sub (lfound ++ acc) <| lx)
   ≡⟨ cong (sub rfound <|_) (amgu-unifies lx ly acc (lfound ++ acc) req) ⟩
     sub rfound <| (sub (lfound ++ acc) <| ly)
   ≡⟨ sym (<|-assoc (sub rfound) (sub (lfound ++ acc)) ly) ⟩
     (sub rfound <> sub (lfound ++ acc)) <| ly
   ≡⟨ <|-≗ ly (sym ∘ (sub-++ rfound (lfound ++ acc))) ⟩
     sub (rfound ++ (lfound ++ acc)) <| ly
   ∎)
   (amgu-unifies rx ry (lfound ++ acc) (rfound ++ (lfound ++ acc)) eq)
  where open ≡.≡-Reasoning

amgu-unifies (′ x) (′ y) [] σ eq = flexFlex-unifies x y σ (Maybeₚ.just-injective eq)

-- FIXME: factor out
amgu-unifies (′ x) top [] σ eq = flexRigid-unifies x top eq
amgu-unifies (′ x) (# t) [] σ eq = flexRigid-unifies x (# t) eq
amgu-unifies (′ x) < l , r > [] σ eq = flexRigid-unifies x < l , r > eq
amgu-unifies top (′ y) [] σ eq = sym (flexRigid-unifies y top eq)
amgu-unifies (# s) (′ y) [] σ eq = sym (flexRigid-unifies y (# s) eq)
amgu-unifies < l , r > (′ y) [] σ eq = sym (flexRigid-unifies y < l , r > eq)

amgu-unifies s t (acc -, z ↦ r) σ eq with amgu-acc s t (acc -, z ↦ r) σ eq
amgu-unifies s t (acc -, (z ↦ r)) .((found ++ acc) -, (z ↦ r)) eq | found , refl
  rewrite <|-assoc (sub (found ++ acc)) (r for z) s
  | <|-assoc (sub (found ++ acc)) (r for z) t
  | amgu-step acc z r s t
  = amgu-unifies (r for z <| s) (r for z <| t) acc (found ++ acc) (Maybeₚ.map-injective (λ {refl → refl}) eq)



mgu-unifies : (s t : Type m) (σ : AList m n) → mgu s t ≡ just (n , σ) → sub σ <| s ≡ sub σ <| t
mgu-unifies s t σ eq = amgu-unifies s t [] σ eq
