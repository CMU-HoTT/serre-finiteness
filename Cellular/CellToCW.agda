module Cellular.CellToCW where

import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cellular.CellComplex
open import Cellular.Connectivity
open import Cellular.CW
open import Cellular.EmptyFamily
open import Cellular.RelativeCellComplex
open import Pushout.IsPushout

private
  variable
    ℓ ℓ' : Level

-- A (finite) cell complex is also a [0,e)-cell complex for some e.
isBddCellComplex : {X Y : Type} (f : X → Y) → Type
isBddCellComplex f = ∃[ e ∈ ℕ ] isRelativeCellComplex (rangeFamily 0 e) f

isCellComplex→isBddCellComplex : {X Y : Type} (f : X → Y)
  → isRelativeCellComplex standardFamily f → isBddCellComplex f
isCellComplex→isBddCellComplex =
  isRCCElimProp standardFamily isBddCellComplex (λ _ → isPropPropTrunc)
  ∣ 0 , isRCC-idfun _ ∣₁
  (λ f g hf hg → do
    (ef , hf') ← hf
    (eg , hg') ← hg
    let e = max ef eg
    return (e ,
      isRCC-comp (rangeFamily 0 e)
        (isRCC-familyGenerates _ _ (rangeFamilyGenerates 0 e 0 ef ≤-refl left-≤-max) hf')
        (isRCC-familyGenerates _ _ (rangeFamilyGenerates 0 e 0 eg ≤-refl right-≤-max) hg')))
  (λ {i} → ∣ suc i , isRCC-base _ (i , zero-≤ , ≤-refl) ∣₁)
  λ f k → map (λ (e , hf) → e , isRCC-po _ isPushoutOfInr hf)

-- If X is a [0,e)-cell complex then there is
-- a (d-1)-dimensional CW complex X_d
-- together with a relative [d,e)-cell complex g : X_d → X.
-- We prove this by induction on d.
-- Mainly interested in the case d = e,
-- so that g must be an equivalence.
module _ (e : ℕ) where
  open GoodFactorization
  toCW-dim : (d : ℕ)
    (X : Type) (hX : isRelativeCellComplex (rangeFamily 0 e) (Empty.rec {A = X}))
    → ∥ Σ[ C ∈ dimCW.T d ] Σ[ g ∈ (dimCW.ty C → X) ] isRelativeCellComplex (rangeFamily d e) g ∥₁
  toCW-dim 0 X hX = ∣ tt , _ , hX ∣₁
  toCW-dim (suc d) X hX = do
    (C , g , rg) ← toCW-dim d X hX
    r ← hasGoodFactorization d e g rg
    let i = isPushoutOf→Pushout≃ (r .hg)
    return ((C , r .N , r .hg .fst) , r .h ∘ equivFun i , isRCC-comp _ (isRCC-equiv _ i) (r .hh))

  toCW : (X : Type) (hX : isRelativeCellComplex (rangeFamily 0 e) (Empty.rec {A = X}))
    → ∥ Σ[ C ∈ FinCW ] FinCW-ty C ≃ X ∥₁
  toCW X hX = do
    (C , g , hg) ← toCW-dim e X hX
    return ((e , C) , g , equivOfRCCEmpty (rangeFamily e e) (λ (i , hei , hie) → <-asym hie hei) hg)

isCellComplex→isFinCW : {X : Type} → isCellComplex X → isFinCW X
isCellComplex→isFinCW {X} hX = do
  (e , h') ← isCellComplex→isBddCellComplex (Empty.rec {A = X}) hX
  toCW e X h'
