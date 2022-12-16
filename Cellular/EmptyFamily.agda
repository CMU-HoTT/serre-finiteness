module Cellular.EmptyFamily where

open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation

open import Cellular.RelativeCellComplex
open import Pushout.IsPushout using (compIsEquiv)

private
  variable
    ℓi ℓ ℓ' : Level

-- TODO[cubical]: generalize universe levels in
-- Cubical.HITs.PropositionalTruncation.Properties
rec' : {A : Type ℓ} {P : Type ℓ'} → isProp P → (A → P) → ∥ A ∥₁ → P
rec' Pprop f ∣ x ∣₁ = f x
rec' Pprop f (squash₁ x y i) = Pprop (rec' Pprop f x) (rec' Pprop f y) i

module _ (ℐ : Family {ℓi = ℓi} {ℓ = ℓ}) (hℐ : Family.Ix ℐ → ⊥) where
  private
    open relativeCellComplex
    rccEmpty : {X : Type ℓ} (c : T ℐ X) → isEquiv (fun ℐ c)
    rccEmpty (0 , _) = idIsEquiv _
    rccEmpty (suc m , i , _) = Empty.elim (hℐ i)

  equivOfRCCEmpty : {X Y : Type ℓ} {f : X → Y} → isRelativeCellComplex ℐ f → isEquiv f
  equivOfRCCEmpty = rec' (isPropIsEquiv _)
    (λ (c , g , e) → subst isEquiv e (compIsEquiv (rccEmpty c) (equivIsEquiv g)))
