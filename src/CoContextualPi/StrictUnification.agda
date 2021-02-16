{- Based on ideas from:
   - Conor McBride's First Order Unification by Structural Recursion
   - Wen Kokke's mechanisation, which introduces (var | con) terms
   - Ulf Norell's use of universes to avoid using mutual recursion to appease the termination checker
-}

open import Function using (_∘_; id)
open import Relation.Nullary using (Dec; yes; no; _because_; does)
open import Relation.Nullary.Decidable as Dec using ()
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Category.Functor
open import Category.Monad
open import Category.Applicative

open import Data.Bool.Base as Bool using (true; false)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product as Product using (∃; ∃-syntax; Σ; _×_; _,_; proj₁; proj₂)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Fin.Base as Fin using (Fin; zero; suc)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)

import Data.Maybe.Categorical as maybeCat
import Data.Fin.Properties as Finₚ
import Data.Nat.Properties as ℕₚ
import Data.Vec.Properties as Vecₚ
import Data.List.Properties as Listₚ


module CoContextualPi.StrictUnification
  (Kind : Set)                   (decEqKind : ∀          (x y : Kind)     → Dec (x ≡ y))
  (Con : Kind → List Kind → Set) (decEqCon  : ∀ {k} {ks} (x y : Con k ks) → Dec (x ≡ y)) where

private
  -- Help ourselves to some goodies
  open RawFunctor {{...}}
  open RawApplicative {{...}} hiding (_<$>_)
  open RawMonad {{...}} hiding (_<$>_; _⊛_)
  instance maybeFunctor = maybeCat.functor
  instance maybeMonad = maybeCat.monad
  instance maybeApplicative = maybeCat.applicative


infix 25 _for_
infixl 20 _<|_
infixr 20 |>

infixr 2 !_
pattern !_ t = _ , t

KindCtx : Set
KindCtx = List Kind

private
  variable
    n m l : ℕ
    i : Fin n
    k k' : Kind
    ks ks' γ δ ξ : KindCtx

data Univ : Set where
  one : Kind → Univ
  all : List Kind → Univ

data _∋_▹_ : KindCtx → Kind → KindCtx → Set where
  zero : (k ∷ γ) ∋ k ▹ γ
  suc  : γ ∋ k ▹ δ → (k' ∷ γ) ∋ k ▹ (k' ∷ δ)

_∋_ : KindCtx → Kind → Set
γ ∋ x = ∃ (γ ∋ x ▹_)

data _⊢_ (γ : KindCtx) : Kind → Set where
  var : γ ∋ k → γ ⊢ k
  con : Con k ks → All (γ ⊢_) ks → γ ⊢ k

_⊢'_ : KindCtx → Univ → Set
γ ⊢' one k = γ ⊢ k
γ ⊢' all ks = All (γ ⊢_) ks

private variable u : Univ


-- Decidable equality on terms
--

var-injective : {x : γ ∋ k} {y : γ ∋ k} → var x ≡ var y → x ≡ y
var-injective refl = refl

suc-injective : {x : γ ∋ k} {y : γ ∋ k} → _≡_ {A = _ ∋ _} (Product.map (k' ∷_) suc x) (Product.map (k' ∷_) suc y) → x ≡ y
suc-injective refl = refl

kind-injective : {nx : Con k ks} {ny : Con k ks'} {asx : All (γ ⊢_) ks} {asy : All (γ ⊢_) ks'}
                  → con nx asx ≡ con ny asy → ks ≡ ks'
kind-injective refl = refl

name-injective : {nx ny : Con k ks} {asx asy : All (γ ⊢_) ks} → con nx asx ≡ con ny asy → nx ≡ ny
name-injective refl = refl

args-injective : {nx ny : Con k ks} {asx asy : All (γ ⊢_) ks} → con nx asx ≡ con ny asy → asx ≡ asy
args-injective refl = refl

decEq-∋ : (x y : γ ∋ k) → Dec (x ≡ y)
decEq-∋ (! zero) (! zero) = yes refl
decEq-∋ (! zero) (! suc y) = no (λ ())
decEq-∋ (! suc x) (! zero) = no (λ ())
decEq-∋ (! suc x) (! suc y) = Dec.map′ (cong (Product.map (_ ∷_) suc)) (suc-injective) (decEq-∋ (! x) (! y))

decEq-⊢ : (x y : γ ⊢' u) → Dec (x ≡ y)
decEq-⊢ {u = one _} (var x) (con s ts) = no λ ()
decEq-⊢ {u = one _} (con s ts) (var x) = no λ ()
decEq-⊢ {u = one _} (var x) (var y) = Dec.map′ (cong var) var-injective (decEq-∋ x y)
decEq-⊢ {u = one i} (con {ks = ksx} nx asx) (con {ks = ksy} ny asy) with Listₚ.≡-dec decEqKind ksx ksy
... | no ax≢ay = no (ax≢ay ∘ kind-injective)
... | yes refl with decEqCon nx ny
...            | no nx≢ny = no (nx≢ny ∘ name-injective)
...            | yes refl with decEq-⊢ asx asy
...                       | no asx≢asy = no (asx≢asy ∘ args-injective)
...                       | yes refl = yes refl
decEq-⊢ {u = all _} [] [] = yes refl
decEq-⊢ {u = all _} (x ∷ xs) (y ∷ ys) with decEq-⊢ x y
decEq-⊢ {u = all _} (x ∷ xs) (y ∷ ys) | no x≢y = no ((x≢y ∘ cong All.head))
decEq-⊢ {u = all _} (x ∷ xs) (y ∷ ys) | yes refl with decEq-⊢ xs ys
decEq-⊢ {u = all _} (x ∷ xs) (y ∷ ys) | yes refl | no xs≢ys = no (xs≢ys ∘ cong All.tail)
decEq-⊢ {u = all _} (x ∷ xs) (y ∷ ys) | yes refl | yes refl = yes refl


-- Renaming and substitutions
--

|> : (γ ∋ k → δ ∋ k) → γ ∋ k → δ ⊢ k
|> f x = var (f x)

_<|_ : (∀ {k} → γ ∋ k → δ ⊢ k) → γ ⊢' u → δ ⊢' u
_<|_ {u = one _} f (var x) = f x
_<|_ {u = one _} f (con n xs) = con n (f <| xs)
_<|_ {u = all _} f [] = []
_<|_ {u = all _} f (x ∷ xs) = (f <| x) ∷ (f <| xs)


_<>_ : (∀ {k} → δ ∋ k → ξ ⊢ k) → (∀ {k} → γ ∋ k → δ ⊢ k) → (γ ∋ k → ξ ⊢ k)
f <> g = f <|_ ∘ g


-- Push in and push out
--

-- A renaming (thin x) pushes up everithing x and above
thin : δ ∋ k' ▹ γ → γ ∋ k → δ ∋ k
thin zero (! y) = ! suc y
thin (suc x) (! zero) = ! zero
thin (suc x) (! suc y) = Product.map _ suc (thin x (! y))

-- A renaming (thick x) tries to lower everything above x
-- Only succeeds if x itself is not present
thick : γ ∋ k' ▹ δ → γ ∋ k → (δ ∋ k) ⊎ (k ≡ k')
thick zero (! zero) = inj₂ refl
thick zero (! suc y) = inj₁ (! y)
thick (suc x) (! zero) = inj₁ (! zero)
thick (suc x) (! suc y) = Sum.map₁ (Product.map _ suc) (thick x (! y))

-- Substitution of one particular variable
--

_for_ : δ ⊢ k → γ ∋ k ▹ δ → γ ∋ k' → δ ⊢ k'
(t for x) y = Sum.[ var , (λ {refl → t}) ] (thick x y)

-- Defunctionalize sequences of substitutions
--

data Subst : KindCtx → KindCtx → Set where
  [] : Subst γ γ
  _-,_↦_ : Subst γ δ → ξ ∋ k ▹ γ → γ ⊢ k → Subst ξ δ


idSubst : ∃ (Subst γ)
idSubst = _ , []

singleSubst : δ ∋ k ▹ γ → γ ⊢ k → ∃ (Subst δ)
singleSubst i t = _ , ([] -, i ↦ t)

_++_ : Subst γ δ → Subst ξ γ → Subst ξ δ
xs ++ [] = xs
xs ++ (ys -, z ↦ r) = (xs ++ ys) -, z ↦ r

sub : Subst γ δ → (γ ∋ k → δ ⊢ k)
sub [] = var
sub (σs -, x ↦ t) = sub σs <> (t for x)


-- insertion : γ ∋ k → ∃ (Insertion k γ)
-- insertion zero = _ , zero
-- insertion (suc x) = Product.map (_ ∷_) suc (insertion x)

-- Occurs check, lowers the term if the variable is not present
--

check : δ ∋ k' ▹ γ → δ ⊢' u → Maybe (γ ⊢' u)
check {u = one _} i (var x) = Sum.[ just ∘ var , (λ _ → nothing) ] (thick i x)
check {u = one _} i (con n as) = con n <$> check i as
check {u = all _} i [] = just []
check {u = all _} i (x ∷ xs) = _∷_ <$> check i x ⊛ check i xs


-- Unification algorithm
--

-- Substitute variable x with variable y
flexFlex : δ ∋ k ▹ γ → δ ∋ k → ∃ (Subst δ)
flexFlex x y = Sum.[ singleSubst x ∘ var , (λ _ → idSubst) ] (thick x y)

-- Substitute variable x with term t
flexRigid : δ ∋ k ▹ γ → δ ⊢ k → Maybe (∃ (Subst δ))
flexRigid x t = singleSubst x <$> check x t


amgu : γ ⊢' u → γ ⊢' u → ∃ (Subst γ) → Maybe(∃ (Subst γ))
amgu {u = all _} [] [] acc                    = just acc
amgu {u = all _} (x ∷ xs) (y ∷ ys) acc        = amgu x y acc >>= amgu xs ys
amgu {u = one _} (var (! x)) (var y) (_ , []) = just (flexFlex x y)
amgu {u = one _} (var (! x)) t (_ , [])       = flexRigid x t
amgu {u = one _} s (var (! x)) (_ , [])       = flexRigid x s
amgu {u = one _} (con {ks = kx} nx asx) (con {ks = ky} ny asy) acc
    with Listₚ.≡-dec decEqKind kx ky
... | false because _ = nothing
... | yes refl with does (decEqCon nx ny)
...            | false = nothing
...            | true = amgu asx asy acc
amgu {u = one _} s t (_ , acc -, z ↦ r) =
  Product.map₂ (_-, z ↦ r) <$> amgu ((r for z) <| s) ((r for z) <| t) (_ , acc)


{-
unify : UTerm u m → UTerm u m → Maybe(∃ (Subst m))
unify s t = amgu s t idSubst
-}
