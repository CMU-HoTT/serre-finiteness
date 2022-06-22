module ConnectedCover where

open import Cubical.Foundations.Everything

open import Cubical.Algebra.Group.EilenbergMacLane.Base
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.HITs.Truncation
open import Cubical.Homotopy.Connected

open import HomotopyGroups
open import FibCofibSeq

private
  variable
    ℓ : Level

postulate
  -- n+3 (or n+1, depending on the convention) connected cover
  _⦉_⦊ : (X : Pointed ℓ) → ℕ → Pointed ℓ
  1ConnCovEq : (X : Pointed ℓ) (scX : isConnected 3 (typ X))
    → X ≡ (X ⦉ 0 ⦊)
  Conn→ConnConnCov : (X : Pointed ℓ) (m n : ℕ)
    → isConnected m (typ X) → isConnected m (typ (X ⦉ n ⦊))
  ConnCovIsConn : (X : Pointed ℓ) (n : ℕ)
    → isConnected (3 + n) (typ (X ⦉ n ⦊))
  πConnCov : (X : Pointed ℓ) (n k : ℕ) → k ≥ n
    → (πAb (suc k) (X ⦉ n ⦊)) ≡ (πAb (suc k) X)
  ⦉-⦊EMFibSeq : (X : Pointed ℓ) (n : ℕ)
    → FiberSeq (EM∙ (πAb n X) (suc n)) (X ⦉ (suc n) ⦊) (X ⦉ n ⦊)

