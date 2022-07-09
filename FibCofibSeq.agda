module FibCofibSeq where

open import Cubical.Foundations.Everything

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.Unit
open import Cubical.Data.Nat
open import Cubical.Homotopy.Loopspace

open import PointedHITs
open import HomotopyGroups

private
  variable
    ℓ : Level

-- fits better w/ singletons
fiber' : {A B : Type ℓ} → (A → B) → B → Type ℓ
fiber' {A = A} f a = Σ[ x ∈ A ] f x ≡ a

postulate
  CofiberSeq : Pointed ℓ → Pointed ℓ → Pointed ℓ → Type ℓ
  -- CofiberSeq A B C = Σ[ f ∈ A →∙ B ] Σ[ g ∈ B →∙ C ] Σ[ h ∈ g ∘∙ f = const∙ A C ], ...
  -- Probably use a record.

  copuppe : {A B C : Pointed ℓ} → CofiberSeq A B C → CofiberSeq B C (S∙ A)

  FiberSeq : Pointed ℓ → Pointed ℓ → Pointed ℓ → Type ℓ
  -- likewise


  puppe : {X Y Z : Pointed ℓ} → FiberSeq X Y Z → FiberSeq (Ω Z) X Y


fiber∙ : {A B : Pointed ℓ} → (A →∙ B) → Pointed ℓ
fiber∙ {A = A} {B = B} f = fiber (fst f) (pt B) , (pt A) , (snd f)

postulate
  FiberFiberSeq : (A B : Pointed ℓ) (f : A →∙ B)
    → FiberSeq (fiber∙ f) A B

  BaseEqFiberSeq : (A B C C' : Pointed ℓ) → C ≡ C' → FiberSeq A B C 
    → FiberSeq A B C'

  TotalEqFiberSeq : (A B B' C : Pointed ℓ) → B ≡ B' → FiberSeq A B C
    → FiberSeq A B' C

  FiberEqFiberSeq : (A A' B C : Pointed ℓ) → A ≡ A' → FiberSeq A B C
    → FiberSeq A' B C

  ContrBase→TotalEqFib : (A B C : Pointed ℓ) → isContr (typ C)
    → FiberSeq A B C → A ≡ B

postulate
  -- Check the LES file
  ExactSequenceIsomorphism : (A B C : Pointed ℓ) (n : ℕ) → FiberSeq A B C
    → (AbGroupEquiv {ℓ} {ℓ} (πAb (suc n) C) UnitAbGroup) → (AbGroupEquiv {ℓ} {ℓ} (πAb n C) UnitAbGroup)
    → AbGroupEquiv (πAb n A) (πAb n B)

