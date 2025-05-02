{-# OPTIONS --lossy-unification #-}
module FiberOrCofiberSequences.CofiberBase where

open import Everything

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation renaming (rec to propRec)
open import Cubical.HITs.Pushout
open import Cubical.HITs.SetTruncation renaming (elim to setElim)
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.LES

open import PointedHITs

open import ConnectedCovers.TruncationLevelFacts
open import FiniteCW
open import Pullback.IsPullback

private
  variable
    ℓ : Level


postulate
  CofiberSeq : Pointed ℓ → Pointed ℓ → Pointed ℓ → Type ℓ
  -- CofiberSeq A B C = Σ[ f ∈ A →∙ B ] Σ[ g ∈ B →∙ C ] Σ[ h ∈ g ∘∙ f = const∙ A C ], ...
  -- Probably use a record.

  CofiberSeqDom : {A B C : Pointed ℓ} → CofiberSeq A B C → Pointed ℓ

  CofiberSeqDom-Id : {A B C : Pointed ℓ} {S : CofiberSeq A B C}
                      → CofiberSeqDom S ≡ A

  CofiberSeqExt : {A B C : Pointed ℓ} → CofiberSeq A B C → Pointed ℓ

  CofiberSeqExt-Id : {A B C : Pointed ℓ} {S : CofiberSeq A B C}
                     → CofiberSeqExt S ≡ B

  CofiberSeqCof : {A B C : Pointed ℓ} → CofiberSeq A B C → Pointed ℓ

  CofiberSeqCof-Id : {A B C : Pointed ℓ} {S : CofiberSeq A B C}
                     → CofiberSeqCof S ≡ C

  CofiberSeqInc : {A B C : Pointed ℓ} (S : CofiberSeq A B C)
                  → ((CofiberSeqDom S) →∙ (CofiberSeqExt S))

  CofiberSeqProj : {A B C : Pointed ℓ} (S : CofiberSeq A B C)
                   → ((CofiberSeqExt S) →∙ (CofiberSeqCof S))

  CofiberSeqExact : {A B C : Pointed ℓ} {S : CofiberSeq A B C}
                    → (CofiberSeqProj S) ∘∙ (CofiberSeqInc S)
                        ≡ ((λ _ → snd (CofiberSeqCof S)) , refl)

  cofiber-CofiberSeq : {A B : Pointed ℓ} (f : A →∙ B)
    → CofiberSeq A B (cofib (fst f) , inl tt)

  isFinCWCofiberSeq : {A B C : Pointed ℓ} {S : CofiberSeq A B C}
                      → (isFinCW (typ (CofiberSeqDom S)))
                      → (isFinCW (typ (CofiberSeqExt S)))
                      → (isFinCW (typ (CofiberSeqCof S)))

  CofiberSeqMap : {A B C A' B' C' : Pointed ℓ}
    (S : CofiberSeq A B C) (S' : CofiberSeq A' B' C')
    (f : (CofiberSeqDom S) →∙ (CofiberSeqDom S'))
    (g : (CofiberSeqExt S) →∙ (CofiberSeqExt S'))
    → (g ∘∙ CofiberSeqInc S) ≡ (CofiberSeqInc S' ∘∙ f)
    → ((CofiberSeqCof S) →∙ (CofiberSeqCof S'))

  CofiberSeqMapConn : (n : ℕ) {A B C A' B' C' : Pointed ℓ}
    (S : CofiberSeq A B C) (S' : CofiberSeq A' B' C')
    (f : (CofiberSeqDom S) →∙ (CofiberSeqDom S'))
    (g : (CofiberSeqExt S) →∙ (CofiberSeqExt S'))
    (p : (g ∘∙ CofiberSeqInc S) ≡ (CofiberSeqInc S' ∘∙ f))
    → isConnectedFun n (fst f)
    → isConnectedFun n (fst g)
    → isConnectedFun n (fst (CofiberSeqMap S S' f g p))

-- cofiber sequences for unpointed maps
postulate
  CofiberSeq₋ : Type ℓ → Type ℓ → Pointed ℓ → Type ℓ

  CofiberSeqDom₋ : {A B : Type ℓ} {C : Pointed ℓ}
                   → CofiberSeq₋ A B C → Type ℓ

  CofiberSeqDom-Id₋ : {A B : Type ℓ} {C : Pointed ℓ} {S : CofiberSeq₋ A B C}
                      → CofiberSeqDom₋ S ≡ A

  CofiberSeqExt₋ : {A B : Type ℓ} {C : Pointed ℓ}
                   → CofiberSeq₋ A B C → Type ℓ

  CofiberSeqExt-Id₋ : {A B : Type ℓ} {C : Pointed ℓ} {S : CofiberSeq₋ A B C}
                     → CofiberSeqExt₋ S ≡ B

  CofiberSeqCof₋ : {A B : Type ℓ} {C : Pointed ℓ}
                   → CofiberSeq₋ A B C → Pointed ℓ

  CofiberSeqCof-Id₋ : {A B : Type ℓ} {C : Pointed ℓ} {S : CofiberSeq₋ A B C}
                     → CofiberSeqCof₋ S ≡ C

  CofiberSeqInc₋ : {A B : Type ℓ} {C : Pointed ℓ} (S : CofiberSeq₋ A B C)
                  → ((CofiberSeqDom₋ S) → (CofiberSeqExt₋ S))

  CofiberSeqProj₋ : {A B : Type ℓ} {C : Pointed ℓ} (S : CofiberSeq₋ A B C)
                   → ((CofiberSeqExt₋ S) → typ (CofiberSeqCof₋ S))

  CofiberSeqExact₋ : {A B : Type ℓ} {C : Pointed ℓ} {S : CofiberSeq₋ A B C}
                    → (CofiberSeqProj₋ S) ∘ (CofiberSeqInc₋ S)
                        ≡ (λ _ → snd (CofiberSeqCof₋ S))

  cofiber-CofiberSeq₋ : {A B : Type ℓ} (f : A → B)
    → CofiberSeq₋ A B (cofib f , inl tt)

  isFinCWCofiberSeq₋ : {A B : Type ℓ} {C : Pointed ℓ} {S : CofiberSeq₋ A B C}
                      → (isFinCW (CofiberSeqDom₋ S))
                      → (isFinCW (CofiberSeqExt₋ S))
                      → (isFinCW (typ (CofiberSeqCof₋ S)))

  CofiberSeqMap₋ : {A B A' B' : Type ℓ} {C C' : Pointed ℓ}
    (S : CofiberSeq₋ A B C) (S' : CofiberSeq₋ A' B' C')
    (f : (CofiberSeqDom₋ S) → (CofiberSeqDom₋ S'))
    (g : (CofiberSeqExt₋ S) → (CofiberSeqExt₋ S'))
    → (g ∘ CofiberSeqInc₋ S) ≡ (CofiberSeqInc₋ S' ∘ f)
    → ((CofiberSeqCof₋ S) →∙ (CofiberSeqCof₋ S'))

  CofiberSeqMapConn₋ : (n : ℕ) {A B A' B' : Type ℓ} {C C' : Pointed ℓ}
    (S : CofiberSeq₋ A B C) (S' : CofiberSeq₋ A' B' C')
    (f : (CofiberSeqDom₋ S) → (CofiberSeqDom₋ S'))
    (g : (CofiberSeqExt₋ S) → (CofiberSeqExt₋ S'))
    (p : (g ∘ CofiberSeqInc₋ S) ≡ (CofiberSeqInc₋ S' ∘ f))
    → isConnectedFun n f
    → isConnectedFun n g
    → isConnectedFun n (fst (CofiberSeqMap₋ S S' f g p))
