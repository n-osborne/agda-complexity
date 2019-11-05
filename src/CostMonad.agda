open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

module CostMonad where

-- the CostMonad and its primitive
data _costs_ (A : Set) (n : ℕ) : Set where
  compute : A → A costs n

-- sometimes, we just want the raw data (without its cost)
raw : {A : Set}{n : ℕ} → A costs n → A
raw (compute a) = a

-- return does not change the raw data, but it changes the type
return : {A : Set}(a : A) → A costs 0
return = compute

-- bind operators - two definitions are given in order to facilitate the proofs
infixl 1 _>>=₁_
_>>=₁_ : {A B : Set}{n m : ℕ} → A costs n → (A → B costs m) → B costs (m + n)
compute a >>=₁ f = compute (raw (f a))

infixl 1 _>>=₂_
_>>=₂_ : {A B : Set}{n m : ℕ} → A costs n → (A → B costs m) → B costs (n + m)
compute a >>=₂ f = compute (raw (f a))

-- Propositional Equality is a Substitutive Relation:
same-cost-≡ : ∀ {A : Set}{n m : ℕ} → n ≡ m → A costs n → A costs m
same-cost-≡ = subst (_costs_ _)

-- lift takes an unary function and makes it an atomic operation
-- (Note: use partial application for n-ary functions with n > 1)
lift : {A B : Set} → (A → B) → (A → B costs 1)
lift f = λ x → compute (f x)

private
  open import Data.Vec hiding (_>>=_)
  open import Data.Bool

  -- foldr with atomic operation
  foldr-compute₁ : {A B : Set}{n : ℕ} → (v : Vec A n) → (A → B → B costs 1) → B → B costs n
  foldr-compute₁ [] f b = compute b
  foldr-compute₁ (x ∷ xs) f b = foldr-compute₁ xs f b >>=₁ λ b' → f x b'

  -- foldr with non-atomic operation
  foldr-compute : {A B : Set}{n k : ℕ} → (v : Vec A n) → (A → B → B costs k) → B → B costs (n * k)
  foldr-compute [] f b = compute b
  foldr-compute (x ∷ xs) f b = same-cost-≡ refl (foldr-compute xs f b >>=₁ λ b' → f x b')

  -- map with atomic operation
  map-compute₁ : {A B : Set}{n : ℕ} → (A → B costs 1) → Vec A n → (Vec B n) costs n
  map-compute₁ f [] = compute []
  map-compute₁ f (x ∷ xs) = f x >>=₂ λ b → compute (b ∷ raw (map-compute₁ f xs))

  -- map with non-atomic operation
  map-compute : {A B : Set}{n k : ℕ} → (A → B costs k) → Vec A n → (Vec B n) costs (n * k)
  map-compute f [] = compute []
  map-compute f (x ∷ xs) = f x >>=₂ λ b → compute (b ∷ (raw (map-compute f xs)))

  postulate
    A   : Set
    as₃ : Vec A 3
    f   : A → Bool costs 1
    f₂  : A → Bool costs 2
    g   : Bool → Bool → Bool costs 1
    
  ex₁ : Bool costs 3
  ex₁ = foldr-compute (true ∷ true ∷ false ∷ []) g true

  ex₂ : Vec Bool 3 costs 3
  ex₂ = map-compute f as₃

  ex₃ : Vec Bool 3 costs 6
  ex₃ = map-compute f₂ as₃
