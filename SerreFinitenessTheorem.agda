{-# OPTIONS --without-K #-}

module SerreFinitenessTheorem where

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Foundations.Everything
open import Cubical.Homotopy.Connected


private
  variable
    ℓ : Level

open import Outline hiding (saf→isFPπ; saf→saf⦉-⦊)

postulate
  silly : (n : ℕ) → n ≥ n

isFPId : (X : Pointed ℓ) (n : ℕ) → isFP (πAb (suc n) (X ⦉ n ⦊)) ≡  isFP (πAb (suc n) X)
isFPId X n = λ i → isFP (πConnCov X n n (silly n) i)

interleaved mutual
  saf→isFPπ : (X : Pointed ℓ) (safX : saf X) (scX : isConnected 3 (typ X)) (n : ℕ)
    → isFP (πAb n X)
  saf→saf⦉-⦊ : (X : Pointed ℓ) (safX : saf X) (scX : isConnected 3 (typ X)) (n : ℕ)
    → saf (X ⦉ n ⦊)
  saf→isFPπ X safX scX 0 = saf→isFPBottomπ X safX 0 scX
  saf→saf⦉-⦊ X safX scX 0 = transport (λ i → saf (1ConnCovEq X scX i)) safX
  saf→isFPπ X safX scX (suc n) = transport (isFPId X n) (saf→Conn→isFPπ (X ⦉ n ⦊) (saf→saf⦉-⦊ X safX scX n) (suc n) (ConnCovIsConn X n))
  saf→saf⦉-⦊ X safX scX (suc n) = safTotal (⦉-⦊EMFibSeq X n) (Conn→ConnConnCov X 3 n scX) (saf→saf⦉-⦊ X safX scX n) (isFP→safEM (πAb n X) (saf→isFPπ X safX scX n) n)
   

