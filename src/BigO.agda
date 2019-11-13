----------------------------------------------------------
-- project : agda-complexity
-- file    : BigO.agda
-- content : Big O relation Definition
-- author  : Nicolas Osborne
----------------------------------------------------------


module BigO where
  open import Filter public
  open import Data.Nat hiding (_⊔_)
  open import Level hiding (suc; zero)
  open import Relation.Binary
--  open import Data.Product


  -- Big O relation between two functions (A → ℕ)
  -- The constant and the lesser bound is to be given at construction
  data BigO {c ℓ₁ ℓ₂ : Level}{A : Set c}{eq : Rel A ℓ₁}{ord : Rel A ℓ₂}
              {P : IsPartialOrder eq ord}{k : ℕ}{a : A}
              (f : A → ℕ)(g : A → ℕ) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
    bigO : ∀ (x : A) → Filter A eq ord P a x → (f x) ≤ (k * (g x)) → BigO f g

  -- Omega relation between two functions (A → ℕ)
  -- Define by BigO
  data Omega {c ℓ₁ ℓ₂ : Level}{A : Set c}{eq : Rel A ℓ₁}{ord : Rel A ℓ₂}
              {P : IsPartialOrder eq ord}{k : ℕ}{a : A}
              (f : A → ℕ)(g : A → ℕ) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
    homega : BigO {c}{ℓ₁}{ℓ₂}{A}{eq}{ord}{P}{k}{a} g f → Omega f g

  -- Theta relation between two functions (A → ℕ)
  -- Defined by BigO and Omega
  data Theta {c ℓ₁ ℓ₂ : Level}{A : Set c}{eq : Rel A ℓ₁}{ord : Rel A ℓ₂}
             {P : IsPartialOrder eq ord}{k : ℕ}{a : A}
             (f : A → ℕ)(g : A → ℕ) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
    theta : BigO {c}{ℓ₁}{ℓ₂}{A}{eq}{ord}{P}{k}{a} f g →
            Omega {c}{ℓ₁}{ℓ₂}{A}{eq}{ord}{P}{k}{a} f g →
            Theta f g

  
