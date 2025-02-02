module SAF where

open import Everything

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Join
open import Cubical.HITs.Truncation
open import Cubical.HITs.Susp

open import FiniteCW
open import PointedHITs
open import FPAbGroup
open import HomotopyGroups

open import FiberOrCofiberSequences.Base

private
  variable
    ℓ : Level

-- stably almost finite spaces

-- possibly this exists elsewhere
Susp^ : ℕ → Type ℓ → Type ℓ
Susp^ 0 X = X
Susp^ (suc n) X = Susp (Susp^ n X)

-- (n-1)-finite, perhaps?
nFinite : HLevel → Type ℓ → Type ℓ
nFinite {ℓ} n X =
  ∥ (Σ[ C ∈ FinCW ℓ ] Σ[ f ∈ (decodeFinCW C → X) ] isConnectedFun n f) ∥ 1

nFinite-isProp : {n : HLevel} {X : Type ℓ} → isProp (nFinite n X)
nFinite-isProp = isOfHLevelTrunc 1

-- should change to use pointed suspension
stablyNFinite : HLevel → Pointed ℓ → Type ℓ
stablyNFinite {ℓ} n X = ∥ (Σ[ m ∈ ℕ ] nFinite (m + n) (Susp^ m (typ X))) ∥ 1

stablyNFinite-isProp : {n : HLevel} {X : Pointed ℓ} → isProp (stablyNFinite n X)
stablyNFinite-isProp = isOfHLevelTrunc 1

saf : Pointed ℓ → Type ℓ
saf X = (n : ℕ) → stablyNFinite n X

saf' : Pointed ℓ → Type ℓ
saf' X = ∥ ((n : ℕ) → (Σ[ m ∈ ℕ ] nFinite (m + n) (Susp^ m (typ X)))) ∥ 1

saf-isProp : {X : Pointed ℓ} → isProp (saf X)
saf-isProp {X = X} = isPropΠ (λ n → stablyNFinite-isProp {n = n} {X = X})

saf'-isProp : {X : Pointed ℓ} → isProp (saf' X)
saf'-isProp = isOfHLevelTrunc 1

-- depends on the implementation of FinCW, postulate skeleton function
-- seems wrong
postulate
  isFinCW→saf : {X : Pointed ℓ} → isFinCW (typ X) → saf X

  isFinCW→saf' : {X : Pointed ℓ} → isFinCW (typ X) → saf' X

postulate
  stablyNFiniteOfSusp : (n : HLevel) (A : Pointed ℓ)
    → stablyNFinite (suc n) (S∙ A) → stablyNFinite n A

  stablyNFiniteExtension : {n : HLevel} {A B C : Pointed ℓ} (S : CofiberSeq A B C)
    → stablyNFinite n A → stablyNFinite n C → stablyNFinite n B

  safCofiber : {A B C : Pointed ℓ} → CofiberSeq A B C
    → saf A → saf B → saf C

  saf'Cofiber : {A B C : Pointed ℓ} → CofiberSeq A B C
    → saf' A → saf' B → saf' C

  safExtension : {A B C : Pointed ℓ} → CofiberSeq A B C
    → saf A → saf C → saf B

  saf'Extension : {A B C : Pointed ℓ} → CofiberSeq A B C
    → saf' A → saf' C → saf' B

  safS¹× : {A : Pointed ℓ} → saf A → saf (S¹∙ ×∙ A)

  saf'S¹× : {A : Pointed ℓ} → saf' A → saf' (S¹∙ ×∙ A)

  -- TODO: Most likely the inequalities on `k` are not quite right
  stablyNFiniteJoin : {X₁ X₂ : Pointed ℓ} (m₁ n₁ m₂ n₂ : HLevel)
    (hXm₁ : isConnected m₁ (typ X₁)) (hXn₁ : stablyNFinite n₁ X₁)
      (hXm₂ : isConnected m₂ (typ X₂)) (hXn₂ : stablyNFinite n₂ X₂)
    (k : HLevel) (hk₁ : n₁ + m₂ ≤ k) (hk₂ : m₁ + n₂ ≤ k)
    → stablyNFinite k (join∙ X₁ X₂)

  stablyNFiniteApprox : {X Y : Pointed ℓ} (f : X →∙ Y)
    (n : HLevel) (hf : isConnectedFun n (fst f))
    → stablyNFinite (1 + n) X → stablyNFinite n Y

  stablyNFiniteApprox' : {X Y : Pointed ℓ} (f : X →∙ Y)
    (n : HLevel) (hf : isConnectedFun n (fst f))
    → stablyNFinite n Y → stablyNFinite n X


