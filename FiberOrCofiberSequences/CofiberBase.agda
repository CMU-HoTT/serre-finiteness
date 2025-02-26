{-# OPTIONS --lossy-unification #-}
module FiberOrCofiberSequences.CofiberBase where

open import Everything

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation renaming (rec to propRec)
open import Cubical.HITs.SetTruncation renaming (elim to setElim)
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.LES

open import PointedHITs

open import ConnectedCovers.TruncationLevelFacts
open import Pullback.IsPullback

private
  variable
    ℓ : Level


postulate
  CofiberSeq : Pointed ℓ → Pointed ℓ → Pointed ℓ → Type ℓ
  -- CofiberSeq A B C = Σ[ f ∈ A →∙ B ] Σ[ g ∈ B →∙ C ] Σ[ h ∈ g ∘∙ f = const∙ A C ], ...
  -- Probably use a record.
