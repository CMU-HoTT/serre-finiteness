{-# OPTIONS --lossy-unification #-}
module FiberOrCofiberSequences.CofiberBase where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

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

open import Cubical.CW.Base

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
    → isConnectedFun (1 + n) (fst g)
    → isConnectedFun (1 + n) (fst (CofiberSeqMap S S' f g p))

-- cofiber sequences for unpointed maps
postulate
  CofiberSeq₋ : Type ℓ → Type ℓ → Pointed ℓ → Type ℓ

  CofiberSeqDom₋ : {A B : Type ℓ} {C : Pointed ℓ}
                   → CofiberSeq₋ A B C → Type ℓ

  CofiberSeqDom-Eq₋ : {A B : Type ℓ} {C : Pointed ℓ} {S : CofiberSeq₋ A B C}
                      → CofiberSeqDom₋ S ≃ A

  CofiberSeqDom-Id₋ : {A B : Type ℓ} {C : Pointed ℓ} {S : CofiberSeq₋ A B C}
                      → CofiberSeqDom₋ S ≡ A

  CofiberSeqExt₋ : {A B : Type ℓ} {C : Pointed ℓ}
                   → CofiberSeq₋ A B C → Type ℓ

  CofiberSeqExt-Eq₋ : {A B : Type ℓ} {C : Pointed ℓ} {S : CofiberSeq₋ A B C}
                      → CofiberSeqExt₋ S ≃ B

  CofiberSeqExt-Id₋ : {A B : Type ℓ} {C : Pointed ℓ} {S : CofiberSeq₋ A B C}
                     → CofiberSeqExt₋ S ≡ B

  CofiberSeqCof₋ : {A B : Type ℓ} {C : Pointed ℓ}
                   → CofiberSeq₋ A B C → Pointed ℓ

  CofiberSeqCof-Eq₋ : {A B : Type ℓ} {C : Pointed ℓ} {S : CofiberSeq₋ A B C}
                      → CofiberSeqCof₋ S ≃∙ C

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

  cofiber-CofiberSeqInc₋ : {A B : Type ℓ} (f : A → B)
    → f ≡ equivFun CofiberSeqExt-Eq₋
           ∘ CofiberSeqInc₋ (cofiber-CofiberSeq₋ f)
           ∘ invEq CofiberSeqDom-Eq₋

  isFinCWCofiberSeq₋ : {A B : Type ℓ} {C : Pointed ℓ} {S : CofiberSeq₋ A B C}
                      → (isFinCW (CofiberSeqDom₋ S))
                      → (isFinCW (CofiberSeqExt₋ S))
                      → (isFinCW (typ (CofiberSeqCof₋ S)))

  cofiberDom-isFinCWCofiberSeq₋ : {A B : Type ℓ} (f : A → B)
                                  → isFinCW A
                                  → isFinCW (CofiberSeqDom₋
                                       (cofiber-CofiberSeq₋ f))


  cofiberExt-isFinCWCofiberSeq₋ : {A B : Type ℓ} (f : A → B)
                                  → isFinCW B
                                  → isFinCW (CofiberSeqExt₋
                                       (cofiber-CofiberSeq₋ f))

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
    → isConnectedFun (1 + n) g
    → isConnectedFun (1 + n) (fst (CofiberSeqMap₋ S S' f g p))

  CofiberSeqMap-mix : {A B : Type ℓ} {C A' B' C' : Pointed ℓ}
    (S : CofiberSeq₋ A B C) (S' : CofiberSeq A' B' C')
    (f : (CofiberSeqDom₋ S) → typ (CofiberSeqDom S'))
    (g : (CofiberSeqExt₋ S) → typ (CofiberSeqExt S'))
    → (g ∘ CofiberSeqInc₋ S) ≡ ((fst (CofiberSeqInc S')) ∘ f)
    → ((CofiberSeqCof₋ S) →∙ (CofiberSeqCof S'))

  CofiberSeqMapConn-mix : (n : ℕ) {A B : Type ℓ} {C A' B' C' : Pointed ℓ}
    (S : CofiberSeq₋ A B C) (S' : CofiberSeq A' B' C')
    (f : (CofiberSeqDom₋ S) → typ (CofiberSeqDom S'))
    (g : (CofiberSeqExt₋ S) → typ (CofiberSeqExt S'))
    (p : (g ∘ CofiberSeqInc₋ S) ≡ ((fst (CofiberSeqInc S')) ∘ f))
    → isConnectedFun n f
    → isConnectedFun (1 + n) g
    → isConnectedFun (1 + n) (fst (CofiberSeqMap-mix S S' f g p))

  CofiberSeqMap-cofiber : {A B : Type ℓ} {A' B' C' : Pointed ℓ}
    (m : A → B) (S' : CofiberSeq A' B' C')
    (f : A → typ (CofiberSeqDom S'))
    (g : B → typ (CofiberSeqExt S'))
    → (g ∘ m) ≡ ((fst (CofiberSeqInc S')) ∘ f)
    → ((CofiberSeqCof₋ (cofiber-CofiberSeq₋ m)) →∙ (CofiberSeqCof S'))

  CofiberSeqMapConn-cofiber : (n : ℕ) {A B : Type ℓ} {A' B' C' : Pointed ℓ}
    (m : A → B) (S' : CofiberSeq A' B' C')
    (f : A → typ (CofiberSeqDom S'))
    (g : B → typ (CofiberSeqExt S'))
    (p : (g ∘ m) ≡ ((fst (CofiberSeqInc S')) ∘ f))
    → isConnectedFun n f
    → isConnectedFun (1 + n) g
    → isConnectedFun (1 + n) (fst (CofiberSeqMap-cofiber m S' f g p))

  CofiberSeq₋→CofiberSeq : {A B C : Pointed ℓ}
    (S : CofiberSeq₋ (typ A) (typ B) C)
    (p : equivFun CofiberSeqExt-Eq₋
           (CofiberSeqInc₋ S
            (invEq CofiberSeqDom-Eq₋ (pt A))) ≡ pt B)
    → CofiberSeq A B C
