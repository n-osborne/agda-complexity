open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

module CostMonad where

-- the CostMonad and its primitive
data _costs_ (A : Set) (n : ℕ) : Set where
  compl : A → A costs n

raw : {A : Set}{n : ℕ} → A costs n → A
raw (compl a) = a

return : {A : Set}{n : ℕ}(a : A) → A costs n
return = compl

_>>=_ : {A B : Set}{n m : ℕ} → A costs n → (A → B costs m) → B costs (n + m)
compl a >>= f = return (raw (f a))


-- Proposiitonal Equality is a Substitutive Relation:
same-cost-≡ : ∀ {A : Set}{n m : ℕ} → n ≡ m → A costs n → A costs m
same-cost-≡ = subst (_costs_ _)

