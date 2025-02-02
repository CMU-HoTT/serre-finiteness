module CorollariesToHurewicz where

open import Everything

open import Cubical.Data.Nat
open import Cubical.Homotopy.Connected

open import FiniteCW
open import FPAbGroup
open import HomotopyGroups
open import SAF

private
  variable
    ℓ : Level

postulate
  -- Bottom homotopy groups, e.g.,
  -- if n = 0 we are talking about π₂(X),
  -- and X must be simply connected = 1-connected.
  isFinCW→isFPBottomπ : (X : Pointed ℓ) (hX : isFinCW (typ X))
    (n : ℕ) (cX : isConnected (3 + n) (typ X))
    → isFP (πAb n X)

  -- Could weaken hypothesis to stablyNFinite n X (or so).
  saf→isFPBottomπ : (X : Pointed ℓ) (hX : saf X)
    (n : ℕ) (cX : isConnected (3 + n) (typ X))
    → isFP (πAb n X)

