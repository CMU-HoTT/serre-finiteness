module CorollariesToGanea where

open import Everything

open import Cubical.Algebra.AbGroup
open import Cubical.Data.Nat
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.EilenbergMacLane.Base
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

postulate
  isFP→safEM : (A : AbGroup ℓ) (fpA : isFP A) (n : ℕ)
    → saf (EM∙ A (suc n))

