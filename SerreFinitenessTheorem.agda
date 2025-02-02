{-# OPTIONS --lossy-unification #-}
module SerreFinitenessTheorem where

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Everything
open import Cubical.Homotopy.Connected


private
  variable
    ℓ : Level

open import SAF
open import FPAbGroup
open import HomotopyGroups
open import ConnectedCovers.Base
open import ConnectedCovers.EMIsFiber
open import CorollariesToHurewicz
open import CorollariesToGanea

isFPId : (X : Pointed ℓ) (n : ℕ) → isFP (πAb n (X < (suc n) >)) ≡  isFP (πAb n X)
isFPId X n = λ i → isFP (πConnCovEq X n n ≤-refl i)

mutual
  saf→isFPπ : (X : Pointed ℓ) (safX : saf X) (scX : isConnected 3 (typ X)) (n : ℕ)
    → isFP (πAb n X)
  saf→isFPπ X safX scX zero = saf→isFPBottomπ X safX 0 scX
  saf→isFPπ X safX scX (suc n) =
    transport (isFPId X (suc n)) (saf→isFPBottomπ (X < (2 + n) >) (saf→saf<-> X safX scX (suc n)) (suc n) (ConnCovIsConn X (2 + n)))
  
  saf→saf<-> : (X : Pointed ℓ) (safX : saf X) (scX : isConnected 3 (typ X)) (n : ℕ)
    → saf (X < (suc n) >)
  saf→saf<-> X safX scX 0 = transport (λ i → saf (1ConnCovEq X scX i)) safX
  saf→saf<-> X safX scX (suc n) =
    safTotal (<->EMFibSeq X n) (Conn→ConnConnCov X 3 (suc n) scX)
      (saf→saf<-> X safX scX n) (isFP→safEM (πAb n X) (saf→isFPπ X safX scX n) n)
   

