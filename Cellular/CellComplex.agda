module Cellular.CellComplex where

import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.NatMinusOne
open import Cubical.Foundations.Everything
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout

open import Cellular.RelativeCellComplex
open import Cellular.Fold
open import Pushout.IsPushout

private
  variable
    ℓ : Level

open Family

-- This could be "generalized" to live in an arbitrary universe,
-- but perhaps there is not much use?
standardFamily : Family {ℓi = ℓ-zero} {ℓ = ℓ-zero}
standardFamily .Ix = ℕ
standardFamily .A n = S (-1+ n)
standardFamily .B n = Unit
standardFamily .j n = λ _ → tt

sfSF : SelfFolding standardFamily
sfSF n = subst
  (λ T → isRelativeCellComplex standardFamily (λ (_ : T) → tt))
  (sym PushoutSusp≡Susp)
  (isRCC-base standardFamily (suc n))

isCellComplex : Type → Type
isCellComplex X =
  isRelativeCellComplex standardFamily (Empty.rec {A = X})

module _ {X Y Z P : Type} {f : X → Y} {g : X → Z} {g' : Y → P} {f' : Z → P}
  {α : g' ∘ f ≡ f' ∘ g} (po : isPushout f g g' f' α) where
  -- Cell complexes are closed under pushout.
  isCCPushout : isCellComplex X → isCellComplex Y → isCellComplex Z
    → isCellComplex P
  isCCPushout hX hY hZ = subst (isRelativeCellComplex standardFamily) (funExt Empty.elim) hP'
    where
      hZ' : isRelativeCellComplex standardFamily (g ∘ Empty.rec)
      hZ' = subst (isRelativeCellComplex standardFamily) (funExt Empty.elim) hZ

      hg : isRelativeCellComplex standardFamily g
      hg = cancelRCC-R _ sfSF (Empty.rec {A = X}) g hX hZ'

      hg' : isRelativeCellComplex standardFamily g'
      hg' = isRCC-po _ (f , f' , sym α , transposeIsPushout po) hg

      hP' : isRelativeCellComplex standardFamily (g' ∘ Empty.rec)
      hP' = isRCC-comp _ hY hg'
