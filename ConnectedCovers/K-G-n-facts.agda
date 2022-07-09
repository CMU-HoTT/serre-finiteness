module ConnectedCovers.K-G-n-facts where

open import Cubical.Foundations.Everything

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.EilenbergMacLane.Base
open import Cubical.Algebra.Group.EilenbergMacLane.Properties
open import Cubical.Data.Nat
open import Cubical.Homotopy.Connected

open import HomotopyGroups

private
  variable
    ℓ : Level

postulate
  EMUniqueness : (X : Pointed ℓ) (n : ℕ) → isConnected (3 + n) (typ X)
    → isOfHLevel (4 + n) (typ X) → X ≡ (EM∙ (πAb n X) (2 + n))


  EMAbGrpEq : (G G' : AbGroup ℓ) (n : ℕ) → AbGroupEquiv G G'
    → (EM∙ G n) ≡ (EM∙ G' n)

