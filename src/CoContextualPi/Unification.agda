{- Based on ideas from:
   - Conor McBride's First Order Unification by Structural Recursion
   - Wen Kokke's mechanisation, which introduces (var | con) terms
   - Ulf Norell's use of universes to avoid using mutual recursion to appease the termination checker
-}

open import Function using (_∘_)
open import Relation.Nullary using (Dec; yes; no; _because_; does)
open import Relation.Nullary.Decidable as Dec using ()
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Category.Functor
open import Category.Monad
open import Category.Applicative

open import Data.Bool.Base as Bool using (true; false)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product as Product using (∃; Σ; _×_; _,_; proj₁; proj₂)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Fin.Base as Fin using (Fin; zero; suc)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)

import Data.Maybe.Categorical as maybeCat
import Data.Fin.Properties as Finₚ
import Data.Nat.Properties as ℕₚ
import Data.Vec.Properties as Vecₚ


module CoContextualPi.Unification (Name : ℕ → Set) (decEqName : ∀ {k} (x y : Name k) → Dec (x ≡ y)) where

-- Help ourselves to some goodies
open RawFunctor {{...}}
open RawApplicative {{...}} hiding (_<$>_)
open RawMonad {{...}} hiding (_<$>_; _⊛_)
instance maybeFunctor = maybeCat.functor
instance maybeMonad = maybeCat.monad
instance maybeApplicative = maybeCat.applicative


infix 25 _for_
infixl 20 _<|
infixr 20 |>

private variable n m l k : ℕ

data Univ : Set where
  one : Univ
  vec : ℕ → Univ

data Term (n : ℕ) : Set where
  var : Fin n → Term n
  con : Name k → Vec (Term n) k → Term n

UTerm : Univ → ℕ → Set
UTerm one n = Term n
UTerm (vec k) n = Vec (Term n) k

private variable u : Univ


-- Decidable equality on terms
--

var-injective : {x y : Fin n} → var x ≡ var y → x ≡ y
var-injective refl = refl

arity-injective : ∀ {ax ay} {nx : Name ax} {ny : Name ay} {asx : Vec (Term n) ax} {asy : Vec (Term n) ay}
                → con nx asx ≡ con ny asy → ax ≡ ay
arity-injective refl = refl

name-injective : {nx : Name k} {ny : Name k} {asx : Vec (Term n) k} {asy : Vec (Term n) k}
               → con nx asx ≡ con ny asy → nx ≡ ny
name-injective refl = refl

args-injective : {nx : Name k} {ny : Name k} {asx : Vec (Term n) k} {asy : Vec (Term n) k}
               → con nx asx ≡ con ny asy → asx ≡ asy
args-injective refl = refl

decEqTerm : (x y : UTerm u n) → Dec (x ≡ y)
decEqTerm {u = one} (var x) (con s ts) = no λ ()
decEqTerm {u = one} (con s ts) (var x) = no λ ()
decEqTerm {u = one} (var x) (var y) = Dec.map′ (cong var) var-injective (x Finₚ.≟ y)
decEqTerm {u = one} (con {ax} nx asx) (con {ay} ny asy) with ax ℕₚ.≟ ay
... | no ax≢ay = no (ax≢ay ∘ arity-injective)
... | yes refl with decEqName nx ny
...            | no nx≢ny = no (nx≢ny ∘ name-injective)
...            | yes refl with decEqTerm asx asy
...                       | no asx≢asy = no (asx≢asy ∘ args-injective)
...                       | yes refl = yes refl
decEqTerm {u = vec k} [] [] = yes refl
decEqTerm {u = vec k} (x ∷ xs) (y ∷ ys) with decEqTerm x y
decEqTerm {u = vec k} (x ∷ xs) (y ∷ ys) | no x≢y = no (x≢y ∘ cong Vec.head)
decEqTerm {u = vec k} (x ∷ xs) (y ∷ ys) | yes refl with decEqTerm xs ys
decEqTerm {u = vec k} (x ∷ xs) (y ∷ ys) | yes refl | no xs≢ys = no (xs≢ys ∘ cong Vec.tail)
decEqTerm {u = vec k} (x ∷ xs) (y ∷ ys) | yes refl | yes refl = yes refl


-- Renaming and substitutions
--

|> : (Fin n → Fin m) → Fin n → Term m
|> f = var ∘ f

_<| : (Fin n → Term m) → UTerm u n → UTerm u m
_<| {u = one} f (var x) = f x
_<| {u = one} f (con n as) = con n ((f <|) as)
_<| {u = vec k} f [] = []
_<| {u = vec k} f (x ∷ xs) = (f <|) x ∷ (f <|) xs

_<>_ : (Fin m → Term n) → (Fin l → Term m) → (Fin l → Term n)
f <> g = f <| ∘ g


-- Push in and push out\
--

-- A renaming (thin x) pushes up everithing x and above
thin : Fin (suc n) → Fin n → Fin (suc n)
thin zero y = suc y
thin (suc x) zero = zero
thin (suc x) (suc y) = suc (thin x y)

-- A renaming (thick x) tries to lower everything above x
-- Only succeeds if x itself is not present
thick : Fin (suc n) → Fin (suc n) → Maybe (Fin n)
thick zero zero = nothing
thick zero (suc y) = just y
thick {suc n} (suc x) zero = just zero
thick {suc n} (suc x) (suc y) = suc <$> (thick x y)

-- Substitution of one particular variable
--

_for_ : Term n → Fin (suc n) → Fin (suc n) → Term n
(t for x) y = Maybe.maybe var t (thick x y)


-- Defunctionalize sequences of substitutions
--

data Subst : ℕ → ℕ → Set where
  [] : ∀ {n} → Subst n n
  _-,_↦_ : ∀ {m n} → Subst m n → Fin (suc m) → Term m → Subst (suc m) n

idSubst : ∃ (Subst n)
idSubst = _ , []

singleSubst : Fin (suc n) → Term n → ∃ (Subst (suc n))
singleSubst i t = _ , ([] -, i ↦ t)

_++_ : Subst m n → Subst l m → Subst l n
xs ++ [] = xs
xs ++ (ys -, z ↦ r) = (xs ++ ys) -, z ↦ r

sub : Subst m n → Fin m → Term n
sub [] = var
sub (σs -, x ↦ t) = sub σs <> (t for x)


-- Occurs check, lowers the term if the variable is not present
--

check : Fin (suc n) → UTerm u (suc n) → Maybe (UTerm u n)
check {u = one} i (var x) = var <$> (thick i x)
check {u = one} i (con n as) = con n <$> check i as
check {u = vec k} i [] = just []
check {u = vec k} i (x ∷ xs) = _∷_ <$> check i x ⊛ check i xs


-- Unification algorithm
--

-- Substitute variable x with variable y
flexFlex : Fin m → Fin m → ∃ (Subst m)
flexFlex {suc m} x y = Maybe.maybe (singleSubst x ∘ var) idSubst (thick x y)


-- Substitute variable x with term t
flexRigid : Fin m → Term m → Maybe (∃ (Subst m))
flexRigid {suc m} x t = singleSubst x <$> check x t


amgu : UTerm u m → UTerm u m → ∃ (Subst m) → Maybe(∃ (Subst m))
amgu {u = vec _} [] [] acc              = just acc
amgu {u = vec _} (x ∷ xs) (y ∷ ys) acc  = amgu x y acc >>= amgu xs ys
amgu {u = one} (var x) (var y) (_ , []) = just (flexFlex x y)
amgu {u = one} (var x) t (_ , [])       = flexRigid x t
amgu {u = one} s (var x) (_ , [])       = flexRigid x s
amgu {u = one} (con {kx} nx asx) (con {ky} ny asy) acc
    with kx ℕₚ.≟ ky
... | false because _ = nothing
... | yes refl with does (decEqName nx ny)
...            | false = nothing
...            | true = amgu asx asy acc
amgu {u = one} s t (_ , acc -, z ↦ r) =
  Product.map₂ (_-, z ↦ r) <$> amgu ((r for z <|) s) ((r for z <|) t) (_ , acc)
