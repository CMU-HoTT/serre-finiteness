{-# OPTIONS --lossy-unification #-}

module ConnectedCovers.Example where

open import Cubical.Foundations.Everything

open import Cubical.Algebra.AbGroup.Base

open import Cubical.Homotopy.EilenbergMacLane.Base

open import Cubical.HITs.Pushout
open import Cubical.HITs.Truncation
open import Cubical.HITs.Wedge

open import ConnectedCovers.Base
open import ConnectedCovers.TruncationLevelFacts

--open import FiberOrCofiberSequences.Base

private
  variable
    ℓ : Level

module _ (A : AbGroup ℓ) (X : Pointed ℓ) where

  Aux : (x : typ (EM∙ A 1 ⋁∙ₗ X))
      → (trunc {X = EM∙ A 1 ⋁∙ₗ X} 3 x) ≡ ∣ inl (snd (EM∙ A 1)) ∣
      → typ (⋁gen∙ (typ A) λ _ → X)
  Aux (inl x) p = pt (⋁gen∙ (typ A) λ _ → X)
  Aux (inr x) p = {!!}
  Aux (push a i) p = {!!}

  Claim : typ ((EM∙ A 1 ⋁∙ₗ X) < 1 >) ≃ typ (⋁gen∙ (typ A) λ _ → X)
  Claim = {!!}
