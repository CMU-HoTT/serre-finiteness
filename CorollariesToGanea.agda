{-# OPTIONS --lossy-unification #-}
module CorollariesToGanea where

open import Everything

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.DirectProduct
open import Cubical.Data.Nat
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.Loopspace

open import SAF
open import FPAbGroup

open import FiberOrCofiberSequences.Base

private
  variable
    ℓ : Level

postulate
  safΩ→saf : {B : Pointed ℓ} (cB : isConnected 2 (typ B)) → saf (Ω B) → saf B
  saf→safΩ : {B : Pointed ℓ} (scB : isConnected 3 (typ B)) → saf B → saf (Ω B)
  safTotal : {F E B : Pointed ℓ} (S : FiberSeq F E B) (scB : isConnected 3 (typ B))
    → saf B → saf F → saf E

EMℤMod-saf : (n m : ℕ) → saf {ℓ = ℓ} (EM∙ (ℤMod n) (suc m))
EMℤMod-saf n zero = safΩ→saf (isConnectedEM 1)
                    (transport (λ i → saf (EM≃ΩEM+1∙ {G = ℤMod n} 0 i))
                    (transport (λ i → saf (ua∙ {A = EM∙ (ℤMod n) 0}
                                               (ℤMod-finite n) refl (~ i)))
                               (saf-Fin n _)))
EMℤMod-saf n (suc m) =
  safΩ→saf (isConnectedSubtr 2 (1 + m)
               (transport (λ i → isConnected (+-comm 2 (1 + m) i)
                                    (typ (EM∙ (ℤMod n) (suc (suc m)))))
                          (isConnectedEM (2 + m))))
            (transport (λ i → saf (EM≃ΩEM+1∙ {G = ℤMod n} (suc m) i))
                       (EMℤMod-saf n m))

EMℤ-saf : (m : ℕ) → saf {ℓ = ℓ} (EM∙ ℤ (suc m))
EMℤ-saf zero = transport (λ i → saf (EM₁ℤ (~ i)))
                         (saf-Sn 1)
EMℤ-saf (suc m) =
  safΩ→saf (isConnectedSubtr 2 (1 + m)
               (transport (λ i → isConnected (+-comm 2 (1 + m) i)
                                    (typ (EM∙ ℤ (2 + m))))
                          (isConnectedEM (2 + m))))
               (transport (λ i → saf (EM≃ΩEM+1∙ {G = ℤ} (suc m) i))
                         (EMℤ-saf m))

saf-dir-prod : (H K : AbGroup ℓ)
  → ((n : ℕ) → saf (EM∙ H (suc n)))
  → ((n : ℕ) → saf (EM∙ K (suc n)))
  → (n : ℕ)
  → saf (EM∙ (AbDirProd H K) (suc n))
saf-dir-prod H K hH hK n =
  transport (λ i → saf (EMDirProd H K (suc n) (~ i)))
            (saf× (hH n) (hK n))

isFP→safEM : (A : AbGroup ℓ) (fpA : isFP A) (n : ℕ)
  → saf (EM∙ A (suc n))
isFP→safEM =
  indFP (λ A → (n : ℕ) → saf (EM∙ A (suc n)))
        (λ A → isOfHLevelΠ 1 λ n → saf-isProp {X = EM∙ A (suc n)})
        EMℤMod-saf
        EMℤ-saf
        saf-dir-prod
