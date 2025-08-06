module CorollariesToHurewicz where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed

open import Cubical.Data.Nat
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Group.Base

open import Cubical.CW.Base
open import Cubical.CW.Connected

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup.FinitePresentation

open import FiniteCW
open import FPAbGroup
open import HomotopyGroups
open import SAF

private
  variable
    ℓ : Level

  -- Bottom homotopy groups, e.g.,
  -- if n = 0 we are talking about π₂(X),
  -- and X must be simply connected = 1-connected.
  --*** STOCKHOLM ***
isFinCW→isFPBottomπ : (X : Pointed ℓ) (hX : isFinCW (typ X))
  (n : ℕ) (cX : isConnected (3 + n) (typ X))
  → isFP (πAb n X)
isFinCW→isFPBottomπ X hX n cX =
  subst isFP (AbGroupPath _ _ .fst
    (GroupIso→GroupEquiv (π'Gr≅πGr (suc n) X)))
      (isFinitelyPresented-π'connectedCW X (finCW→CW (_ , hX) .snd) n cX)

postulate
  -- Could weaken hypothesis to stablyNFinite n X (or so).
  -- not stockholm
  saf→isFPBottomπ : (X : Pointed ℓ) (hX : saf X)
    (n : ℕ) (cX : isConnected (3 + n) (typ X))
    → isFP (πAb n X)
