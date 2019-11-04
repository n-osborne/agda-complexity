open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

module CostMonad where

-- the CostMonad and its primitive
data _costs_ (A : Set) (n : ℕ) : Set where
  compl : A → A costs n

-- sometimes, we just want the raw data (without its cost)
raw : {A : Set}{n : ℕ} → A costs n → A
raw (compl a) = a

-- return does not change the raw data, but it changes the type
return : {A : Set}{n : ℕ}(a : A) → A costs n
return = compl

-- bind operation - two definitions are given in order to facilitate the proofs
infixl 1 _>>=₁_
_>>=₁_ : {A B : Set}{n m : ℕ} → A costs n → (A → B costs m) → B costs (m + n)
compl a >>=₁ f = return (raw (f a))

infixl 1 _>>=₂_
_>>=₂_ : {A B : Set}{n m : ℕ} → A costs n → (A → B costs m) → B costs (n + m)
compl a >>=₂ f = return (raw (f a))

-- Propositional Equality is a Substitutive Relation:
same-cost-≡ : ∀ {A : Set}{n m : ℕ} → n ≡ m → A costs n → A costs m
same-cost-≡ = subst (_costs_ _)

private
  open import Data.Vec hiding (_>>=_)

  -- foldr with atomic operation
  foldr-compl₁ : {A B : Set}{n : ℕ} → (v : Vec A n) → (A → B → B costs 1) → B → B costs n
  foldr-compl₁ [] f b = return b
  foldr-compl₁ (x ∷ xs) f b = (foldr-compl₁ xs f b) >>=₁ (λ b' → f x b')

  -- foldr with non-atomic operation
  foldr-compl : {A B : Set}{n k : ℕ} → (v : Vec A n) → (A → B → B costs k) → B → B costs (n * k)
  foldr-compl [] f b = return b
  foldr-compl (x ∷ xs) f b = same-cost-≡ refl ((foldr-compl xs f b) >>=₁ (λ b' → f x b'))

  -- map with atomic operation
  map-compl₁ : {A B : Set}{n : ℕ} → (A → B costs 1) → Vec A n → (Vec B n) costs n
  map-compl₁ f [] = return []
  map-compl₁ f (x ∷ xs) = ((f x) >>=₂ (λ b → return (b ∷ raw (map-compl₁ f xs))))

  -- map with non-atomic operation
  map-compl : {A B : Set}{n k : ℕ} → (A → B costs k) → Vec A n → (Vec B n) costs (n * k)
  map-compl f [] = return []
  map-compl f (x ∷ xs) = ((f x) >>=₂ (λ b → return (b ∷ (raw (map-compl f xs)))))
