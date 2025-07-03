{-# OPTIONS --lossy-unification #-}
module CorollariesToGanea where

open import Everything

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.DirectProduct
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup
open import Cubical.Algebra.AbGroup.Instances.Int renaming (ℤAbGroup to ℤ)
open import Cubical.Algebra.AbGroup.Instances.IntMod renaming (ℤAbGroup/_ to ℤMod)

open import Cubical.Data.Nat
open import Cubical.HITs.Join renaming (inl to inlj ; inr to inrj)
open import Cubical.HITs.Pushout
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.Loopspace

open import Connectedness
open import SAF
open import FPAbGroup

open import FiberOrCofiberSequences.Base

private
  variable
    ℓ : Level

join∙^ : ℕ → (Pointed ℓ) → Pointed ℓ → Pointed ℓ
join∙^ zero F G = F
join∙^ (suc n) F G = join∙ (join∙^ n F G) G

-- silly
postulate
  
  join-iso-join : (X X' Y : Type ℓ)
    → Iso X X' → Iso (join X Y) (join X' Y)

module Ganea^ {A : Pointed ℓ} {B : Pointed ℓ} (f : A →∙ B) where

  mutual
    E : ℕ → (Pointed ℓ)
    E zero = A
    E (suc n) = fib-cofib (p n) , inr (pt (E n))

    p : (n : ℕ) → (E n →∙ B)
    p zero = f
    p (suc n) = (GaneaMap (p n)) , (snd (p n))

  sntychk : (GaneaMap f) ≡ (fst (p 1))
  sntychk = refl

  F : ℕ → (Pointed ℓ)
  F zero = fiber (fst f) (pt B) , pt A , snd f
  F (suc n) = (GaneaFib (p n)) , ((pt (E (1 + n))) , snd (p n))

  join-F : ℕ → (Pointed ℓ)
  join-F n = join∙^ n (F 0) (Ω B)

  Ganea^Iso : (n : ℕ) → Iso (fst (F n)) (fst (join-F n))
  Ganea^Iso zero = idIso
  Ganea^Iso (suc zero) = GaneaIso f
  Ganea^Iso (suc (suc n)) =
    compIso (GaneaIso (p (suc n)))
            (join-iso-join (typ (F (suc n)))
                        (typ (join-F (suc n))) (typ (Ω B))
                        (Ganea^Iso (suc n)))

    

postulate
  safΩ→saf : {B : Pointed ℓ} (cB : isConnected 2 (typ B)) → saf (Ω B) → saf B
  saf→safΩ : {B : Pointed ℓ} (scB : isConnected 3 (typ B)) → saf B → saf (Ω B)
  safTotal : {F E B : Pointed ℓ} (S : FiberSeq F E B) (scB : isConnected 3 (typ B))
    → saf B → saf F → saf E

EMℤMod-saf : (n m : ℕ) → saf {ℓ = ℓ-zero} (EM∙ (ℤMod (suc n)) (suc m))
EMℤMod-saf n zero = safΩ→saf (isConnectedEM 1)
                    (transport (λ i → saf (EM≃ΩEM+1∙ {G = ℤMod (suc n)} 0 i))
                    (transport (λ i → saf (ua∙ {A = EM∙ (ℤMod (suc n)) 0}
                                               (ℤMod-finite n) refl (~ i)))
                               (saf-Fin (suc n) _)))
EMℤMod-saf n (suc m) =
  safΩ→saf (isConnectedSubtr 2 (1 + m)
               (transport (λ i → isConnected (+-comm 2 (1 + m) i)
                                    (typ (EM∙ (ℤMod (suc n)) (suc (suc m)))))
                          (isConnectedEM (2 + m))))
            (transport (λ i → saf (EM≃ΩEM+1∙ {G = ℤMod (suc n)} (suc m) i))
                       (EMℤMod-saf n m))

EMℤ-saf : (m : ℕ) → saf {ℓ = ℓ-zero} (EM∙ ℤ (suc m))
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

isFP→safEM : (A : AbGroup ℓ-zero) (fpA : isFP A) (n : ℕ)
  → saf (EM∙ A (suc n))
isFP→safEM =
  indFP (λ A → (n : ℕ) → saf (EM∙ A (suc n)))
        (λ A → isOfHLevelΠ 1 λ n → saf-isProp {X = EM∙ A (suc n)})
        (λ { zero m → EMℤ-saf m ; (suc n) m → EMℤMod-saf n m})
        saf-dir-prod
