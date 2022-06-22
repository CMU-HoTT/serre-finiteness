module SAF where

open import Cubical.Foundations.Everything

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Homotopy.Connected

open import FiniteCW
open import PointedHITs
open import FibCofibSeq
open import FPAbGroup
open import HomotopyGroups

private
  variable
    ℓ : Level

-- stably almost finite spaces
postulate
  -- (n-1)-finite, perhaps?
  nFinite : HLevel → Type ℓ → Type ℓ
  -- nFinite {ℓ} n X = ∥ Σ[ C ∈ FinCW ℓ ] Σ[ f ∈ (decodeFinCW C → X) ] isConnectedFun n f ∥₁
  nFinite-isProp : {n : HLevel} {X : Type ℓ} → isProp (nFinite n X)

  stablyNFinite : HLevel → Pointed ℓ → Type ℓ
  stablyNFinite-isProp : {n : HLevel} {X : Pointed ℓ} → isProp (stablyNFinite n X)

  saf : Pointed ℓ → Type ℓ
  saf-isProp : {X : Pointed ℓ} → isProp (saf X)

  isFinCW→saf : {X : Pointed ℓ} → isFinCW (typ X) → saf X

  stablyNFiniteOfSusp : (n : HLevel) (A : Pointed ℓ)
    → stablyNFinite (suc n) (S∙ A) → stablyNFinite n A

  stablyNFiniteExtension : {n : HLevel} {A B C : Pointed ℓ} (S : CofiberSeq A B C)
    → stablyNFinite n A → stablyNFinite n C → stablyNFinite n B

  safCofiber : {A B C : Pointed ℓ} → CofiberSeq A B C
    → saf A → saf B → saf C

  safExtension : {A B C : Pointed ℓ} → CofiberSeq A B C
    → saf A → saf C → saf B

  safS¹× : {A : Pointed ℓ} → saf A → saf (S¹∙ ×∙ A)

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


