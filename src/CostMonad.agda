----------------------------------------------------------
-- project : agda-complexity
-- file    : CostMonad.agda
-- content : CostMonad Definition
-- author  : Nicolas Osborne
----------------------------------------------------------

-- This module proposes a way to compute time complexity at the type level
-- in a monad.
-- The CostMonad is widely inspired by Danielsson's Thunk monad.
-- The main difference is that I don't use ticks inside the algorithm.
-- Instead, I propose to use lifted operations.
-- In doing so, I hope to be able to build a framework to define different cost models.

{-# OPTIONS --safe #-}

module CostMonad where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

-- _costs_ datatype is parameterized by a Set and a ℕ
-- the ℕ is a phantom variable: hidden in the type, not visible in the value.
-- Hence the constructor (compute) only take one argument: the type parameter
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


module Examples (A B : Set)(f₁ : A → B costs 1)(f₂ : A → B costs 2)(g : A → B → B costs 2)(b : B) where
  -- a little module to provide some examples with Vectors
  -- should go in a library on its own providing generic programming
  
  open import Data.Vec hiding (_>>=_)

  -- foldr with cost
  foldr-compute : {A B : Set}{n k : ℕ} → (v : Vec A n) → (A → B → B costs k) → B → B costs (n * k)
  foldr-compute [] f b = compute b
  foldr-compute (x ∷ xs) f b = same-cost-≡ refl (foldr-compute xs f b >>=₁ λ b' → f x b')

  -- map with cost
  map-compute : {A B : Set}{n k : ℕ} → (A → B costs k) → Vec A n → (Vec B n) costs (n * k)
  map-compute f [] = compute []
  map-compute f (x ∷ xs) = f x >>=₂ λ b → compute (b ∷ (raw (map-compute f xs)))

  -- some examples
  -- these does not typecheck if you change the cost of the function or the lenght of the Vec 
  ex₁ : Vec A 3 → B costs 6
  ex₁ as₃ = foldr-compute as₃ g b

  ex₂ : Vec A 3 → Vec B 3 costs 3
  ex₂ as₃ = map-compute f₁ as₃

  ex₃ : Vec A 3 → Vec B 3 costs 6
  ex₃ as₃ = map-compute f₂ as₃

