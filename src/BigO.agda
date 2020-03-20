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
              {P : IsPartialOrder eq ord}{k : ℕ}{k>0 : 1 ≤ k}{a : A}
              (f : A → ℕ)(g : A → ℕ) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
    bigO : ∀ (x : A) → Filter A eq ord P a x → (f x) ≤ (k * (g x)) → BigO f g

  -- Omega relation between two functions (A → ℕ)
  -- Define by BigO
  data Omega {c ℓ₁ ℓ₂ : Level}{A : Set c}{eq : Rel A ℓ₁}{ord : Rel A ℓ₂}
              {P : IsPartialOrder eq ord}{k : ℕ}{k>0 : 1 ≤ k}{a : A}
              (f : A → ℕ)(g : A → ℕ) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
    omega : BigO {c}{ℓ₁}{ℓ₂}{A}{eq}{ord}{P}{k}{k>0}{a} g f → Omega f g

  -- Theta relation between two functions (A → ℕ)
  -- Defined by BigO and Omega
  data Theta {c ℓ₁ ℓ₂ : Level}{A : Set c}{eq : Rel A ℓ₁}{ord : Rel A ℓ₂}
             {P : IsPartialOrder eq ord}{k : ℕ}{k>0 : 1 ≤ k}{a : A}
             (f : A → ℕ)(g : A → ℕ) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
    theta : BigO {c}{ℓ₁}{ℓ₂}{A}{eq}{ord}{P}{k}{k>0}{a} f g →
            Omega {c}{ℓ₁}{ℓ₂}{A}{eq}{ord}{P}{k}{k>0}{a} f g →
            Theta f g

  -- g ∈ O(f)
  -- trivial
  bigO-f-f : (c ℓ₁ ℓ₂ : Level) → (A : Set c) → (eq : Rel A ℓ₁) → (ord : Rel A ℓ₂) →
             (P : IsPartialOrder eq ord) → (k : ℕ) → (k>0 : 1 ≤ k) → (a : A) →
             (f : A → ℕ) → (x : A) → Filter A eq ord P a x → f x ≤ (k * (f x)) →
             BigO {c}{ℓ₁}{ℓ₂}{A}{eq}{ord}{P}{k}{k>0}{a} f f
  bigO-f-f c ℓ₁ ℓ₂ A eq ord P k k>0 a f x F prf = bigO x F prf
