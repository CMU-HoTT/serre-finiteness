module Cellular.CW where

open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Fin
open import Cubical.Data.Nat
open import Cubical.Data.NatMinusOne
open import Cubical.Data.Sigma
open import Cubical.Foundations.Everything
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn

open import Cellular.Connectivity using (NCells)
open import Cellular.RelativeCellComplex

private
  variable
    ℓ ℓ' : Level

module dimCW where
  -- `T d` = type of finite (d-1)-dimensional CW complexes
  T : ℕ → Type
  ty : {d : ℕ} (c : T d) → Type

  T 0 = Unit
  T (suc m) =
    Σ[ c ∈ T m ] Σ[ N ∈ ℕ ] (Fin N × S (-1+ m) → ty c)

  ty {0} _ = ⊥
  ty {suc m} (c , N , k) = Pushout (NCells m N) k

FinCW : Type
FinCW = Σ ℕ dimCW.T

FinCW-ty : FinCW → Type
FinCW-ty (d , c) = dimCW.ty c

isFinCW : Type → Type
isFinCW X = ∃[ c ∈ FinCW ] FinCW-ty c ≃ X
