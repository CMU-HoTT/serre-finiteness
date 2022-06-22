module HomotopyGroups where

open import Cubical.Foundations.Everything

open import Cubical.Algebra.AbGroup
open import Cubical.Data.Nat
open import Cubical.Homotopy.Group.Base

private
  variable
    ℓ : Level

postulate
  -- Essentially proven as EH-π in Cubical.Homotopy.Loopspace
  πGr-comm : (n : ℕ) (A : Pointed ℓ) → (a b : typ (πGr (suc n) A))
    → ·π (suc n) a b ≡ ·π (suc n) b a

-- πAb n A = πₙ₊₂(A), as an abelian group
πAb : (n : ℕ) (A : Pointed ℓ) → AbGroup ℓ
πAb n A = Group→AbGroup (πGr (1 + n) A) (πGr-comm n A)

