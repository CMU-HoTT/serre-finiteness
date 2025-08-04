{-# OPTIONS --lossy-unification #-}
--**** STOCKHOLM  ****
module FPAbGroup where

open import Everything

open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.DirectProduct
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup
open import Cubical.Algebra.AbGroup.Instances.Int renaming (ℤAbGroup to ℤ)
open import Cubical.Algebra.AbGroup.Instances.IntMod renaming (ℤAbGroup/_ to ℤMod)
open import Cubical.Algebra.AbGroup.FinitePresentation
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Data.Fin.Inductive
open import Cubical.Data.Int using (+Comm)
open import Cubical.Data.Nat

open import Cubical.HITs.PropositionalTruncation
open import Cubical.Algebra.Group.QuotientGroup
open import Cubical.Algebra.Group.Subgroup

private
  variable
    ℓ : Level

AbGroup₀ = AbGroup ℓ-zero

-- finite sets, arbitrary hLevel
-- postulate
--   Fin : ℕ → Type

-- postulate
--  ℤMod : ℕ → AbGroup₀
--  ℤ : AbGroup₀


ℤMod-finite : (n : ℕ) → fst (ℤMod (suc n)) ≃ (Fin (suc n))
ℤMod-finite n = isoToEquiv (Iso-Fin-InductiveFin (suc n))

-- finitely presented abelian groups
-- postulate
isFP : AbGroup ℓ → Type ℓ
isFP A = ∥ FinitePresentation A ∥₁

isFP-prop : {A : AbGroup ℓ} → isProp (isFP A)
isFP-prop = squash₁

postulate
  indFP : (P : AbGroup₀ → Type ℓ) → (∀ A → isProp (P A))
     → (∀ n → P (ℤMod n))
     → (∀ H K → P H → P K → P (AbDirProd H K))
     → (∀ A → isFP A → (P A))
  
