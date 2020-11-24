open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; _≢_; trans; cong; cong₂; sym; inspect; [_])
open import Relation.Binary.HeterogeneousEquality as ≅ using (_≅_)
open import Relation.Nullary.Negation using (contradiction)

open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product as Product using (Σ; _×_; ∃-syntax; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Fin.Base as Fin using (Fin; zero; suc)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)

import Data.Fin.Properties as Finₚ
import Data.Maybe.Properties as Maybeₚ
import Data.Product.Properties as Productₚ
import Data.Vec.Properties as Vecₚ

open import CoContextualPi.Types
open import CoContextualPi.Unification

module CoContextualPi.Unification.Properties where

private
  variable
    n m l k : ℕ


#-injective : {s t : Type m} → # s ≡ # t → s ≡ t
#-injective refl = refl

<,>-injective : {lx rx ly ry : Type m} → < lx , rx > ≡ < ly , ry > → lx ≡ ly × rx ≡ ry
<,>-injective refl = refl , refl

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

<|-≗ : {f g : Fin n → Type m} → f ≗ g → (t : Type n) → f <| t ≡ g <| t
<|-≗ eq (′ x) = eq x
<|-≗ eq top = refl
<|-≗ eq (# t) = cong #_ (<|-≗ eq t)
<|-≗ eq < l , r > = cong₂ <_,_> (<|-≗ eq l) (<|-≗ eq r)

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
  = <|-≗ (sub-++ xs ys) (Maybe.maybe ′_ t' (thick i t))

++-id : (xs : AList m n) → [] ++ xs ≡ xs
++-id [] = refl
++-id (xs -, x) = cong (_-, x) (++-id xs)

++-assoc : (xs : AList m n) (ys : AList l m) (zs : AList k l) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
++-assoc xs ys [] = refl
++-assoc xs ys (zs -, x) = cong (_-, x) (++-assoc xs ys zs)

data _≣_ : AList m l → AList m k → Set where
  [] :  _≣_ {m = m} [] []
  _-,_ : {xs : AList m l} {ys : AList m k} → xs ≣ ys → (x : Subst m) → (xs -, x) ≣ (ys -, x)

{-
Π-to-≣ : {xs : AList m n} {ys : AList m k} → _≡_ {A = Σ ℕ (AList m)} (n , xs) (k , ys) → xs ≣ ys
Π-to-≣ {xs = []} {[]} eq = []
Π-to-≣ {xs = xs -, x} {ys -, y} eq = {!!}

-,-injective : {xs : AList m n} {ys : AList m l} {x : Subst m} → xs -, x ≅ ys -, x → xs ≅ ys
-,-injective {xs = []} {[]} eq = _≅_.refl
-,-injective {xs = []} {ys -, x} eq = {!eq!}
-,-injective {xs = xs -, x} {ys} eq = {!!}

++-cancel : (xs : AList m n) (ys : AList m k) (zs : AList l m) → xs ++ zs ≅ ys ++ zs → xs ≅ ys
++-cancel xs ys [] eq = eq
++-cancel xs ys (zs -, z) eq = ++-cancel xs ys zs {!-,-injective eq!}
-}

flexFlex-sound : (x y : Fin m) (σ : AList m n) → flexFlex x y ≡ (n , σ) → sub σ x ≡ sub σ y
flexFlex-sound {suc m} x y σ eq with thick x y | inspect (thick x) y
flexFlex-sound {suc m} x y ._ refl | nothing | [ req ] = cong ′_ (thick-thin-no x y req)
flexFlex-sound {suc m} x y ._ refl | just z | [ req ] with thick-thin-yes x y req
flexFlex-sound {suc m} x ._ ._ refl | just z | [ req ] | r , refl
  rewrite thick-nothing x | thick-thin x r = cong ′_ (sym (Maybeₚ.just-injective req))

flexRigid-sound : (x : Fin m) (t : Type m) {σ : AList m n}
                  → flexRigid x t ≡ just (n , σ) → sub σ x ≡ sub σ <| t
flexRigid-sound {suc m} x t eq with check x t | inspect (check x) t
flexRigid-sound {suc m} x t refl | just t' | [ eq ]
  rewrite thick-nothing x | check-thin x t t' eq = begin
    (′_ <| t')
      ≡⟨ <|-≗ (λ y → cong (Maybe.maybe ′_ t') (sym (thick-thin x y))) t' ⟩
    (Maybe.maybe ′_ t' ∘ thick x ∘ thin x) <| t'
      ≡⟨ <|-assoc (Maybe.maybe ′_ t' ∘ thick x) (|> (thin x)) t' ⟩
    (Maybe.maybe ′_ t' ∘ thick x) <| (|> (thin x) <| t')
      ≡⟨ <|-≗ (λ t'' → sym (<|-id _)) (|> (thin x) <| t') ⟩
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

amgu-sound : (s t : Type m) (acc : AList m n) (σ : AList m l)
             → amgu s t acc ≡ just (l , σ) → sub σ <| s ≡ sub σ <| t
amgu-sound top top acc σ eq = refl
amgu-sound (# s) (# t) acc σ eq = cong #_ (amgu-sound s t acc σ eq)
-- FIXME: factor out
amgu-sound < lx , rx > < ly , ry > acc σ eq with amgu lx ly acc | inspect (amgu lx ly) acc
... | just (_ , lσ) | [ req ] with amgu-acc lx ly acc lσ req
... | lfound , refl with amgu-acc rx ry (lfound ++ acc) σ eq
... | rfound , refl = cong₂ <_,_>
  (begin
     (sub (rfound ++ (lfound ++ acc)) <| lx)
   ≡⟨ <|-≗ (sub-++ rfound (lfound ++ acc)) lx ⟩
     (sub rfound <> sub (lfound ++ acc)) <| lx
   ≡⟨ <|-assoc (sub rfound) (sub (lfound ++ acc)) lx ⟩
     sub rfound <| (sub (lfound ++ acc) <| lx)
   ≡⟨ cong (sub rfound <|_) (amgu-sound lx ly acc (lfound ++ acc) req) ⟩
     sub rfound <| (sub (lfound ++ acc) <| ly)
   ≡⟨ sym (<|-assoc (sub rfound) (sub (lfound ++ acc)) ly) ⟩
     (sub rfound <> sub (lfound ++ acc)) <| ly
   ≡⟨ <|-≗ (sym ∘ (sub-++ rfound (lfound ++ acc))) ly ⟩
     sub (rfound ++ (lfound ++ acc)) <| ly
   ∎)
   (amgu-sound rx ry (lfound ++ acc) (rfound ++ (lfound ++ acc)) eq)
  where open ≡.≡-Reasoning

amgu-sound (′ x) (′ y) [] σ eq = flexFlex-sound x y σ (Maybeₚ.just-injective eq)

-- FIXME: factor out
amgu-sound (′ x) top [] σ eq = flexRigid-sound x top eq
amgu-sound (′ x) (# t) [] σ eq = flexRigid-sound x (# t) eq
amgu-sound (′ x) < l , r > [] σ eq = flexRigid-sound x < l , r > eq
amgu-sound top (′ y) [] σ eq = sym (flexRigid-sound y top eq)
amgu-sound (# s) (′ y) [] σ eq = sym (flexRigid-sound y (# s) eq)
amgu-sound < l , r > (′ y) [] σ eq = sym (flexRigid-sound y < l , r > eq)

amgu-sound s t (acc -, z ↦ r) σ eq with amgu-acc s t (acc -, z ↦ r) σ eq
amgu-sound s t (acc -, (z ↦ r)) .((found ++ acc) -, (z ↦ r)) eq | found , refl
  rewrite <|-assoc (sub (found ++ acc)) (r for z) s
  | <|-assoc (sub (found ++ acc)) (r for z) t
  | amgu-step acc z r s t
  = amgu-sound (r for z <| s) (r for z <| t) acc (found ++ acc) (Maybeₚ.map-injective (λ {refl → refl}) eq)


amgu-complete' : (s t : Type m) (acc : AList m n) (vacc : AList n k) (found : AList k l)
               → amgu s t (vacc ++ acc) ≡ just (l , found ++ (vacc ++ acc))
               → amgu (sub acc <| s) (sub acc <| t) vacc ≡ just (l , found ++ vacc)
amgu-complete' s t [] vacc found eq rewrite <|-id s | <|-id t = eq
amgu-complete' s t (acc -, z ↦ r) vacc found eq rewrite amgu-step (vacc ++ acc) z r s t
  with eqq ← amgu-complete' (r for z <| s) (r for z <| t) acc vacc found (Maybeₚ.map-injective (λ {refl → refl}) eq)
  rewrite <|-assoc (sub acc) (r for z) s
  rewrite <|-assoc (sub acc) (r for z) t
  = eqq


amgus-acc : (xs ys : Vec (Type m) n) (acc : AList m k) (σ : AList m l)
          → amgus xs ys acc ≡ just (l , σ)
          → ∃[ found ] (σ ≡ found ++ acc)
amgus-acc [] [] acc .acc refl = [] , sym (++-id _)
amgus-acc (x ∷ xs) (y ∷ ys) acc σ eq with amgu x y acc | inspect (amgu x y) acc
... | just (_ , stσ) | [ steq ] with amgu-acc x y acc stσ steq
... | stfound , refl with amgus-acc xs ys stσ σ eq
... | xsfound , refl = _ , ++-assoc xsfound stfound acc

eq-subst : (xs : AList m n) (ys : AList m l) → _≡_ {A = Σ ℕ (AList m)} (n , xs) (l , ys) → xs ≅ ys
eq-subst xs .xs refl = _≅_.refl

postulate TODO : ∀ {a} {A : Set a} → A

amgu-complete'' : ∀ {len} (xs ys : Vec (Type m) len) (acc : AList m n) (vacc : AList n k) (found : AList k l)
                → amgus xs ys (vacc ++ acc) ≡ just (l , (found ++ vacc) ++ acc)
                → amgus (Vec.map (sub acc <|_) xs) (Vec.map (sub acc <|_) ys) vacc ≡ just (l , (found ++ vacc))
amgu-complete'' [] [] acc vacc found eq with eq-subst _ _ (Maybeₚ.just-injective eq)
amgu-complete'' [] [] acc vacc found eq | rr = TODO
amgu-complete'' (x ∷ xs) (y ∷ ys) acc vacc found eq
  with just (_ , xyσ) ← amgu x y (vacc ++ acc) | [ xyeq ] ← inspect (amgu x y) (vacc ++ acc)
  with just (_ , xsysσ) ← amgus xs ys xyσ | [ xsyseq ] ← inspect (amgus xs ys) xyσ
  with xyfound , refl ← amgu-acc x y (vacc ++ acc) xyσ xyeq
  with xsysfound , refl ← amgus-acc xs ys xyσ xsysσ xsyseq
  rewrite amgu-complete' x y acc vacc xyfound xyeq
  rewrite amgu-complete'' xs ys acc (xyfound ++ vacc) xsysfound TODO
  = cong just (≅.≅-to-≡ TODO) -- (eq-subst (xsysfound ++ (xyfound ++ vacc)) (found ++ vacc) ?))
  where open ≡.≡-Reasoning



amgu-complete''' : ∀ {len} (xs ys : Vec (Type m) len) (acc : AList m n) (found : AList n l)
                 → amgus xs ys acc ≡ just (l , found ++ acc)
                 → amgus (Vec.map (sub acc <|_) xs) (Vec.map (sub acc <|_) ys) [] ≡ just (l , found)
amgu-complete''' xs ys acc found eq rewrite ++-id acc = amgu-complete'' xs ys acc [] found
                                                        (trans (cong (amgus xs ys) (++-id _)) eq)

amgus-sound : (xs ys : Vec (Type m) k) (acc : AList m l) (σ : AList m n)
              → amgus xs ys acc ≡ just (n , σ) → [ sub σ ]⇓ xs ≡ [ sub σ ]⇓ ys
amgus-sound [] [] acc σ eq = refl
amgus-sound (x ∷ xs) (y ∷ ys) acc σ eq
  with just (_ , xyσ) ← amgu x y acc | [ xyeq ] ← inspect (amgu x y) acc
  with just (_ , xsysσ) ← amgus xs ys xyσ | [ xsyseq ] ← inspect (amgus xs ys) xyσ
  with xyfound , refl ← amgu-acc x y acc xyσ xyeq
  with xsysfound , refl ← amgus-acc xs ys xyσ xsysσ xsyseq
  with refl ← eq
  = begin
  (sub (xsysfound ++ (xyfound ++ acc)) <| x) ∷ Vec.map (_<|_ (sub (xsysfound ++ (xyfound ++ acc)))) xs
    ≡⟨ cong₂ _∷_ (<|-≗ (sub-++ xsysfound xyσ) x) (Vecₚ.map-cong (<|-≗ (sub-++ xsysfound (xyfound ++ acc))) xs) ⟩
  ((sub xsysfound <> sub (xyfound ++ acc)) <| x) ∷ Vec.map (_<|_ (sub xsysfound <> sub (xyfound ++ acc))) xs
    ≡⟨ cong₂ _∷_ (<|-assoc (sub xsysfound) (sub (xyfound ++ acc)) x) (Vecₚ.map-cong (<|-assoc (sub xsysfound) (sub (xyfound ++ acc))) xs) ⟩
  (sub xsysfound <| (sub (xyfound ++ acc) <| x)) ∷ Vec.map (((sub xsysfound) <|_) ∘ ((sub (xyfound ++ acc)) <|_)) xs
    ≡⟨ cong₂ _∷_ refl (Vecₚ.map-∘ ((sub xsysfound) <|_) (sub (xyfound ++ acc) <|_) xs) ⟩
  (sub xsysfound <| (sub xyσ <| x)) ∷ Vec.map (_<|_ (sub xsysfound)) (Vec.map (_<|_ (sub (xyfound ++ acc))) xs)
    ≡⟨ cong₂ _∷_ (cong (sub xsysfound <|_) (amgu-sound x y acc (xyfound ++ acc) xyeq)) (amgus-sound (Vec.map (sub (xyfound ++ acc) <|_) xs) (Vec.map (sub (xyfound ++ acc) <|_) ys) [] xsysfound (amgu-complete''' xs ys xyσ xsysfound xsyseq)) ⟩
  (sub xsysfound <| (sub xyσ <| y)) ∷ Vec.map (_<|_ (sub xsysfound)) (Vec.map (_<|_ (sub (xyfound ++ acc))) ys)
    ≡˘⟨ cong₂ _∷_ refl (Vecₚ.map-∘ ((sub xsysfound) <|_) (sub xyσ <|_) ys) ⟩
  (sub xsysfound <| (sub xyσ <| y)) ∷ Vec.map (((sub xsysfound) <|_) ∘ ((sub xyσ) <|_)) ys
    ≡˘⟨ cong₂ _∷_ (<|-assoc (sub xsysfound) (sub xyσ) y) (Vecₚ.map-cong (<|-assoc (sub xsysfound) (sub xyσ)) ys) ⟩
  ((sub xsysfound <> sub xyσ) <| y) ∷ Vec.map (_<|_ (sub xsysfound <> sub xyσ)) ys
    ≡˘⟨ cong₂ _∷_ (<|-≗ (sub-++ xsysfound xyσ) y) (Vecₚ.map-cong (<|-≗ (sub-++ xsysfound xyσ)) ys) ⟩
  (sub (xsysfound ++ xyσ) <| y) ∷ Vec.map (_<|_ (sub (xsysfound ++ xyσ))) ys
    ∎
  where open ≡.≡-Reasoning


unify-sound : (xs ys : Vec (Type m) k) {σ : AList m n}
              → unify xs ys ≡ just (n , σ) → [ sub σ ]⇓ xs ≡ [ sub σ ]⇓ ys
unify-sound xs ys eq = amgus-sound xs ys [] _ eq
