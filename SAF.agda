module SAF where

open import Everything

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.DirectProduct
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin.Inductive
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Join
open import Cubical.HITs.Truncation
open import Cubical.HITs.Susp
open import Cubical.Homotopy.EilenbergMacLane.Base
--open import Cubical.HITs.Sphere
open import Cubical.Algebra.AbGroup.Instances.Int renaming (ℤAbGroup to ℤ)

open import FiniteCW
open import PointedHITs
open import FPAbGroup
open import HomotopyGroups

open import FiberOrCofiberSequences.Base
open import FiberOrCofiberSequences.CofiberBase

private
  variable
    ℓ : Level

-- stably almost finite spaces
postulate
  isEquivTrnspId : {X Y : Type ℓ} (p : X ≡ Y)
    → isEquiv (transport (λ i → p i → X) (λ x → x))

-- spheres with arbitrary universe level?
postulate
  S : ℕ → Pointed ℓ
  

-- (n-1)-finite, perhaps?
nFinite : HLevel → Type ℓ → Type ℓ
nFinite {ℓ} n X =
  ∥ (Σ[ C ∈ FinCW ℓ ] Σ[ f ∈ (decodeFinCW C → X) ] isConnectedFun n f) ∥ 1

nFinite-isProp : {n : HLevel} {X : Type ℓ} → isProp (nFinite n X)
nFinite-isProp = isOfHLevelTrunc 1

-- closure of n-finiteness
postulate
  cofNFinite : {n : ℕ} {X Y Z : Pointed ℓ} → CofiberSeq X Y Z
    → nFinite n (typ X) → nFinite n (typ Y) → nFinite n (typ Z)

-- should change to use pointed suspension
stablyNFinite : HLevel → Pointed ℓ → Type ℓ
stablyNFinite {ℓ} n X = ∥ (Σ[ m ∈ ℕ ] nFinite (m + n) (Susp^ m (typ X))) ∥ 1

stablyNFinite-isProp : {n : HLevel} {X : Pointed ℓ} → isProp (stablyNFinite n X)
stablyNFinite-isProp = isOfHLevelTrunc 1

saf : Pointed ℓ → Type ℓ
saf X = (n : ℕ) → stablyNFinite n X

saf-isProp : {X : Pointed ℓ} → isProp (saf X)
saf-isProp {X = X} = isPropΠ (λ n → stablyNFinite-isProp {n = n} {X = X})

-- depends on the implementation of FinCW
isFinCW→saf : {X : Pointed ℓ} → isFinCW (typ X) → saf X
isFinCW→saf {X = X} hX =
  rec (saf-isProp {X = X}) (λ p n →
                    ∣ 0 , ∣ (fst p) ,
                           ((transport (λ i → (snd p i) → (typ X)) (λ x → x))
                       , isEquiv→isConnected
                          (transport (λ i → (snd p i) → (typ X))
                                      (λ x → x))
                           (isEquivTrnspId (snd p)) n) ∣ ∣)
                           (isFinCW-def-fun hX)

postulate
  arith : ∀ p n → (p + suc n) ≡ suc (p + n)

  -- silly
  saf-Fin : ∀ n (b : Fin n) → saf (Fin n , b)

  EMDirProd : (H K : AbGroup ℓ) (n : ℕ)
    → (EM∙ (AbDirProd H K) n)
       ≡ (EM∙ H n) ×∙ (EM∙ K n)

  EM₁ℤ : (EM∙ {ℓ-zero} ℤ 1) ≡ S 1 --S¹

  saf-Sn : ∀ n → saf (S {ℓ} n)

-- all just arithmetic
stablyNFiniteOfSusp : (n : HLevel) (A : Pointed ℓ)
      → stablyNFinite (suc n) (S∙ A) → stablyNFinite n A
stablyNFiniteOfSusp n A = rec (stablyNFinite-isProp {X = A})
  λ p → ∣ suc (fst p) , rec nFinite-isProp (λ x → ∣ (fst x) , (fst (snd x)) ,
                        transport (λ i → isConnectedFun (arith (fst p) n i)
                                                         (fst (snd x)))
                                  (snd (snd x)) ∣) (snd p) ∣

-- need definitions or helper lemmas about cofiber sequences (and finite CW complexes?)
postulate
  stablyNFiniteExtension : {n : HLevel} {A B C : Pointed ℓ} (S : CofiberSeq A B C)
      → stablyNFinite n A → stablyNFinite n C → stablyNFinite n B
--stablyNFiniteExtension Co hA hC = {!!}

postulate
  safCofiber : {A B C : Pointed ℓ} → CofiberSeq A B C
    → saf A → saf B → saf C
    
  safExtension : {A B C : Pointed ℓ} → CofiberSeq A B C
    → saf A → saf C → saf B

-- hmm
postulate
  saf× : {A B : Pointed ℓ} → saf A → saf B → saf (A ×∙ B)

  safS¹× : {A : Pointed ℓ} → saf A → saf (S¹∙ ×∙ A)

  safS1× : {A : Pointed ℓ} → saf A → saf ((S {ℓ} 1) ×∙ A)

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


