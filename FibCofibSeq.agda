module FibCofibSeq where

open import Cubical.Foundations.Everything

open import Cubical.Homotopy.Loopspace

open import PointedHITs

private
  variable
    ℓ : Level

postulate
  CofiberSeq : Pointed ℓ → Pointed ℓ → Pointed ℓ → Type ℓ
  -- CofiberSeq A B C = Σ[ f ∈ A →∙ B ] Σ[ g ∈ B →∙ C ] Σ[ h ∈ g ∘∙ f = const∙ A C ], ...
  -- Probably use a record.

  copuppe : {A B C : Pointed ℓ} → CofiberSeq A B C → CofiberSeq B C (S∙ A)

  FiberSeq : Pointed ℓ → Pointed ℓ → Pointed ℓ → Type ℓ
  -- likewise

  puppe : {X Y Z : Pointed ℓ} → FiberSeq X Y Z → FiberSeq (Ω Z) X Y

-- finitely presented abelian groups
