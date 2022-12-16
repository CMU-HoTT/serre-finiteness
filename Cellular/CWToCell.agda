module Cellular.CWToCell where

import Cubical.Data.Empty as Empty
open import Cubical.Data.Fin
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation hiding (rec)

open import Cellular.CellComplex
open import Cellular.Connectivity
open import Cellular.CW
open import Cellular.RelativeCellComplex
open import Pushout.Coproduct
open import Pushout.IsPushout

private
  variable
    ℓi ℓ ℓ' : Level

-- TODO[cubical]: move
open Empty
uninhabIsEquiv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → (A → ⊥) → (B → ⊥) → (f : A → B) → isEquiv f
uninhabIsEquiv ¬a ¬b f = isoToIsEquiv isom
  where
  open Iso
  isom : Iso _ _
  isom .fun = f
  isom .inv b = rec (¬b b)
  isom .rightInv b = rec (¬b b)
  isom .leftInv a = rec (¬a a)

isCellComplex-1Cell : (d : ℕ) → isRelativeCellComplex standardFamily (NCells d 1)
isCellComplex-1Cell d =
  isRCC-po _ (ipoOfPO (equivIsPushout {α = refl} e e)) (isRCC-base _ d)
  where
    open Iso
    i : {Y : Type ℓ} → Iso Y (Fin 1 × Y)
    i .fun y = (0 , y)
    i .inv = snd
    i .rightInv p = ≡-× (isContrFin1 .snd _) refl
    i .leftInv y = refl
    e : {Y : Type ℓ} → isEquiv {B = Fin 1 × Y} (λ (y : Y) → (0 , y))
    e = isoToIsEquiv i

isCellComplex-NCells : (d N : ℕ) → isRelativeCellComplex standardFamily (NCells d N)
isCellComplex-NCells d 0 = isRCC-equiv _ (_ , uninhabIsEquiv (¬Fin0 ∘ fst) (¬Fin0 ∘ fst) _)
isCellComplex-NCells d (suc M) =
  isRCC-po _ (addCells' d 1 M) (isRCC-⊎ _ (isCellComplex-1Cell d ) (isCellComplex-NCells d M))

isCellComplex-dimCW : (d : ℕ) (C : dimCW.T d) → isCellComplex (dimCW.ty C)
isCellComplex-dimCW 0 _ = isRCC-equiv _ (_ , uninhabIsEquiv (idfun _) (idfun _) _)
isCellComplex-dimCW (suc d) (C , N , k) =
  subst (isRelativeCellComplex standardFamily) (funExt λ ())
  (isRCC-comp _ (isCellComplex-dimCW d C) (isRCC-po _ isPushoutOfInr (isCellComplex-NCells _ _)))

isFinCW→isCellComplex : {X : Type} → isFinCW X → ∥ isCellComplex X ∥₁
isFinCW→isCellComplex =
  map (λ ((d , C) , g) →
    subst (isRelativeCellComplex standardFamily) (funExt λ ())
    (isRCC-comp _ (isCellComplex-dimCW d C) (isRCC-equiv _ g)))
