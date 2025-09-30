{-# OPTIONS --lossy-unification --safe #-}
module SerreFinitenessTheorem where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma

open import Cubical.Homotopy.Connected
open import Cubical.HITs.Sn hiding (S)

open import SAF
open import FPAbGroup
open import HomotopyGroups
open import ConnectedCovers.Base
open import ConnectedCovers.EMIsFiber
open import CorollariesToHurewicz
open import CorollariesToGanea

private
  variable
    ℓ : Level

isFPId : (X : Pointed ℓ) (n : ℕ) → isFP (πAb n (X < (suc n) >)) ≡ isFP (πAb n X)
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
      (saf→saf<-> X safX scX n) (isFP→safEM' (πAb n X) (saf→isFPπ X safX scX n) n)

-- Universe polymorphic for demonstration purposes,
-- but should get specialized back to spheres in ℓ-zero
isFPπAbSn : {ℓ : Level} (n m : ℕ) → isFP (πAb n (S {ℓ = ℓ} (2 + m)))
isFPπAbSn n m = saf→isFPπ (S (2 + m)) (saf-Sn (2 + m)) rem2 n
  where
  -- copy-pasted from Cubical.Paper.Pi4S3...
  con-lem : (n m : ℕ) → n < m → isConnected (2 + n) (S₊ m)
  con-lem n m l = isConnectedSubtr (suc (suc n)) (fst l)
             (subst (λ n → isConnected n (S₊ m))
               (sym (+-suc (fst l) (suc n) ∙ cong suc (snd l)))
                (sphereConnected m))

  rem1 : isConnected 3 (S₊ (2 + m))
  rem1 = con-lem 1 (2 + m) (suc-≤-suc (suc-≤-suc zero-≤))

  rem2 : isConnected 3 (S (2 + m) .fst)
  rem2 = isConnectedRetractFromIso 3 rUnit*×Iso rem1
