----------------------------------------------------------
-- project : agda-complexity
-- file    : Filter.agda
-- content : Filter Definition
-- author  : Nicolas Osborne
----------------------------------------------------------

-- This module proposes a Filter which is a way to modelize the property
-- of BigO notation (the property of being ultimately true)
-- I follow here the idea of Gnéneau, Charguéraud and Pottier 2018 in order
-- to define 𝑶-notation with a Filter
-- Though, I prefer to use the definition of a Filter using the Poset
-- rather than as a subset of the powerset of a set

open import Level renaming (suc to lsuc; zero to ℓ0)
open import Relation.Binary
open import Data.Product

module Filter where

  -- *Definition*
  -- ============
  
  -- A Filter is a special subset on a Poset, namely the subset of all
  -- the elements which are greater or equal to a given element of the Poset
  -- according to the partial order relation of the said Poset
  data Filter {c ℓ₁ ℓ₂}(A : Set c)(eq : Rel A ℓ₁)(ord : Rel A ℓ₂)
               (P : IsPartialOrder eq ord)(a : A) :
               A → Set (ℓ₁ ⊔ ℓ₂) where
    filter : (x : A) → ord a x → Filter A eq ord P a x

  -- *Properties*
  -- ============
  
  -- A Filter is never the empty set
  -- A filter contains at least the minimum appearing in its definition
  F-nonemptiness : ∀ {c ℓ₁ ℓ₂ : Level}(A : Set c)(eq : Rel A ℓ₁)(ord : Rel A ℓ₂)
                   (P : IsPartialOrder eq ord)(a : A) →
                   ∃[ x ] Filter A eq ord P a x
  F-nonemptiness A eq ord P a = a ,
                                filter a
                                (IsPreorder.reflexive (IsPartialOrder.isPreorder P)
                                  (IsEquivalence.refl
                                  (IsPreorder.isEquivalence (IsPartialOrder.isPreorder P))))

  -- A Filter is filter base (downward directed: every pair of elements is bounded below)
  F-filter-base : ∀ {c ℓ₁ ℓ₂ : Level}(A : Set c)(eq : Rel A ℓ₁)(ord : Rel A ℓ₂)
                (P : IsPartialOrder eq ord)(a x y : A) →
                Filter A eq ord P a x →
                Filter A eq ord P a y →
                ∃[ z ] Filter A eq ord P a z
  F-filter-base A eq ord P a x y = λ _ → _,_ y

  -- A Filter is upward closed (is an upper set)
  F-upward-closed : ∀ {c ℓ₁ ℓ₂ : Level}(A : Set c)(eq : Rel A ℓ₁)(_≤_ : Rel A ℓ₂)
                (P : IsPartialOrder eq _≤_)(a x y : A) →
                Filter A eq _≤_ P a x →
                x ≤ y →
                Filter A eq _≤_ P a y
  F-upward-closed A eq _≤_ P a x y (filter x (a≤x)) x≤y = filter y (IsPreorder.trans (IsPartialOrder.isPreorder P) a≤x x≤y)                

 -- *Examples*
 -- ==========
 
  private
    open import Relation.Binary.PropositionalEquality
    open import Data.Nat hiding (_⊔_)
    open import Data.Nat.Properties
    -- some exemples of instanciation of Filter
    mkNatFilter : (a : ℕ) → (x : ℕ) → a ≤ x → Filter ℕ _≡_ _≤_ ≤-isPartialOrder a x
    mkNatFilter a x a≤x = filter x a≤x
  
    ex₁ : Filter ℕ _≡_ _≤_ ≤-isPartialOrder 2 3
    ex₁ = mkNatFilter 2 3 (s≤s (s≤s z≤n))
  
    gt3 = mkNatFilter 3
  
    ex₂ : Filter ℕ _≡_ _≤_ ≤-isPartialOrder 3 3
    ex₂ = gt3 3 (s≤s (s≤s (s≤s z≤n)))

  
