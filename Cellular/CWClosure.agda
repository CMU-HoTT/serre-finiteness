module Cellular.CWClosure where

open import Cubical.Data.Empty as Empty using (⊥ ; uninhabEquiv)
open import Cubical.Data.Fin
open import Cubical.Data.Nat
open import Cubical.Data.NatMinusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (rec)
open import Cubical.Data.Unit
open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn

open import Cellular.CellComplex
open import Cellular.CellToCW
open import Cellular.Connectivity using (oneCell ; NCells)
open import Cellular.CW
open import Cellular.CWToCell
open import Pushout.Coproduct
open import Pushout.IsPushout

private
  variable
    ℓ ℓ' ℓ'' : Level

open Iso
-- TODO: Merge with other occurrence
Fin1×Iso : {Y : Type ℓ} → Iso Y (Fin 1 × Y)
Fin1×Iso .fun y = (fzero , y)      -- why did 0 work in the other place?
Fin1×Iso .inv = snd
Fin1×Iso .rightInv p = ≡-× (isContrFin1 .snd _) refl
Fin1×Iso .leftInv y = refl

isFinCWUnit : isFinCW Unit
isFinCWUnit = ∣ (1 , tt , 1 , snd) , isPushoutOf→Pushout≃ (ipoOfPO po) ∣₁
  where
    po : isPushout (NCells 0 1) snd snd (oneCell 0) refl
    po = equivIsPushout (isoToIsEquiv (invIso Fin1×Iso)) (isoToIsEquiv (invIso Fin1×Iso))

isFinCWEmpty : isFinCW ⊥
isFinCWEmpty = ∣ (0 , tt) , idEquiv _ ∣₁

module _ {X Y Z P : Type} {f : X → Y} {g : X → Z} {g' : Y → P} {f' : Z → P}
  {α : g' ∘ f ≡ f' ∘ g} (po : isPushout f g g' f' α) where
  isFinCWPushout : isFinCW X → isFinCW Y → isFinCW Z → isFinCW P
  isFinCWPushout hX hY hZ = isCellComplex→isFinCW
    (isCCPushout po (isFinCW→isCellComplex hX) (isFinCW→isCellComplex hY) (isFinCW→isCellComplex hZ))

-- TODO: Move to module CW, and use it to prove isFinCW→isCellComplex
isFinCWRec : (P : (X : Type) → Type ℓ') (hP : {X : Type} → isProp (P X))
  → P Unit → P ⊥ → ({X Y Z : Type} {f : X → Y} {g : X → Z} → P X → P Y → P Z → P (Pushout f g))
  → {X : Type} → isFinCW X → P X
isFinCWRec P hP hP1 hP0 hPp hX =
  rec hP (λ ((d , C) , g) → subst P (ua g) (aux d C)) hX
  where
    hP0* : P Empty.⊥*
    hP0* = subst P (ua (uninhabEquiv (idfun _) (λ ()))) hP0

    fin× : (N : ℕ) (A : Type) → P A → P (Fin N × A)
    fin× 0 A hPA = subst P (ua (uninhabEquiv (idfun _) (¬Fin0 ∘ fst))) hP0
    fin× (suc N) A hPA = subst P (ua e) (hPp hP0* hPA (fin× N A hPA))
      where
        e : Pushout (Empty.rec* {A = A}) (Empty.rec* {A = Fin N × A}) ≃ Fin (1 + N) × A
        e =
          isPushoutOf→Pushout≃ (ipoOfPO SumIsPushout0) ∙ₑ
          ⊎-equiv (isoToEquiv Fin1×Iso) (idEquiv _) ∙ₑ
          invEquiv Σ⊎≃ ∙ₑ
          ≃-× (isoToEquiv (invIso (Fin+≅Fin⊎Fin _ _))) (idEquiv _)

    hPS : (d : ℕ) → P (S (-1+ d))
    hPS 0 = hP0
    hPS (suc d) = subst P (PushoutSusp≡Susp) (hPp (hPS d) hP1 hP1)

    aux : (d : ℕ) (C : dimCW.T d) → P (dimCW.ty C)
    aux 0 _ = hP0
    aux (suc d) (C , N , k) = hPp (fin× _ _ (hPS d)) (fin× _ _ hP1) (aux d C)
