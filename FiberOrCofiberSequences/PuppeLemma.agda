{-# OPTIONS --lossy-unification #-}
module FiberOrCofiberSequences.PuppeLemma where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Homotopy.Loopspace

open import PointedHITs

open import FiberOrCofiberSequences.Base
open import FiberOrCofiberSequences.CofiberBase

open import LastMinuteLemmas.SuspLemmas

private
  variable
    ℓ : Level

∙IsoOnLeft : {A : Type ℓ} {a b c : A} (p : a ≡ b) → Iso (b ≡ c) (a ≡ c)
Iso.fun (∙IsoOnLeft p) = p ∙_
Iso.inv (∙IsoOnLeft p) = (sym p) ∙_
Iso.rightInv (∙IsoOnLeft p) q =
  assoc p (sym p) q ∙ cong (_∙ q) (rCancel p) ∙ lUnit q ⁻¹
Iso.leftInv (∙IsoOnLeft p) q =
  assoc (sym p) p q ∙ cong (_∙ q) (lCancel p) ∙ lUnit q ⁻¹

∙IsoOnRight : {A : Type ℓ} {a b c : A} (p : b ≡ c) → Iso (a ≡ b) (a ≡ c)
Iso.fun (∙IsoOnRight p) = _∙ p
Iso.inv (∙IsoOnRight p) = _∙ (sym p)
Iso.rightInv (∙IsoOnRight p) q =
  sym (assoc _ _ _) ∙ cong (q ∙_) (lCancel p) ∙ rUnit q ⁻¹
Iso.leftInv (∙IsoOnRight p) q =
  sym (assoc _ _ _) ∙ cong (q ∙_) (rCancel p) ∙ rUnit q ⁻¹

puppeTotalIso : {B C : Pointed ℓ} (f : B →∙ C) →
  Σ[ H ∈ Iso (typ (fiber∙ (inclOfFiberFiberSeq f))) (typ (Ω C)) ]
  Iso.fun H  (pt (fiber∙ (inclOfFiberFiberSeq f))) ≡ (pt (Ω C))
Iso.fun (fst (puppeTotalIso f)) ((b' , q) , p) = (snd f) ⁻¹ ∙ cong (fst f) (p ⁻¹) ∙ q
Iso.inv (fst (puppeTotalIso {B = B} f)) p = (pt B , snd f ∙ p) , refl
Iso.rightInv (fst (puppeTotalIso f)) p = cong (snd f ⁻¹ ∙_) (lUnit (snd f ∙ p) ⁻¹) ∙ assoc (snd f ⁻¹) (snd f) p ∙ cong (_∙ p) (lCancel (snd f)) ∙ lUnit p ⁻¹
Iso.leftInv (fst (puppeTotalIso f)) ((b' , q) , p) =
  ΣPathP
  ((ΣPathP (p ⁻¹
         , toPathP (transportPathLemmaLeft (cong (fst f) (p ⁻¹))
                     (snd f ∙ Iso.fun (fst (puppeTotalIso f))
         ((b' , q) , p)) ∙ cong (cong (fst f) (p ⁻¹) ⁻¹ ∙_)
         (assoc (snd f) (snd f ⁻¹) (cong (fst f) (p ⁻¹) ∙ q)
                                      ∙ cong
                                      (_∙ (cong (fst f) (p ⁻¹) ∙ q))
                   (rCancel (snd f))) ∙ cong (cong (fst f) (p ⁻¹) ⁻¹ ∙_)
                   (lUnit (cong (fst f) (p ⁻¹) ∙ q) ⁻¹)
                   ∙ assoc (cong (fst f) (p ⁻¹) ⁻¹) (cong (fst f) (p ⁻¹)) q
                   ∙ cong (_∙ q) (lCancel (cong (fst f) (p ⁻¹)))
                   ∙ lUnit q ⁻¹)))
        , toPathP (transportPathLemmaLeft (p ⁻¹) refl ∙ rUnit p ⁻¹))
snd (puppeTotalIso f) = cong (snd f ⁻¹ ∙_) (lUnit _ ⁻¹) ∙ lCancel (snd f)


postulate
  copuppe : {A B C : Pointed ℓ} → CofiberSeq A B C → CofiberSeq B C (S∙ A)

-- corollaries

  copuppe-Cof : {n : ℕ} {A B C : Pointed ℓ} → CofiberSeq A B C
             → CofiberSeq (Susp∙^ n A) (Susp∙^ n B) (Susp∙^ n C)

  
  copuppe-Dom : {n : ℕ} {A B C : Pointed ℓ} → CofiberSeq A B C
             → CofiberSeq (Susp∙^ n B) (Susp∙^ n C) (Susp∙^ (suc n) A)

  
  copuppe-Ext : {n : ℕ} {A B C : Pointed ℓ} → CofiberSeq A B C
             → CofiberSeq (Susp∙^ n C) (Susp∙^ (suc n) A) (Susp∙^ (suc n) B)

puppeFiberFiberCase : {B C : Pointed ℓ} (f : B →∙ C)
  → FiberSeq (Ω C) (fiber∙ f) B
puppeFiberFiberCase {B = B} {C = C} f =
  FiberIsoFiberSeq
  ( fst (puppeTotalIso f))
  ( snd (puppeTotalIso f))
  ( FiberFiberSeq
    ( inclOfFiberFiberSeq f))

isoForPuppe : {X Y Z : Pointed ℓ} (F : FiberSeq X Y Z)
              → Iso (typ (fiber∙ (FiberSeqProj F))) (typ X)
isoForPuppe F =
  J (λ Y p → Iso (typ (fiber∙ (FiberSeqProj F))) (typ Y))
    idIso
    (λ i → fst ((FiberSeq.eqFib F) (~ i)))

isoForPuppe∙ : {X Y Z : Pointed ℓ} (F : FiberSeq X Y Z)
               → Iso.fun (isoForPuppe F) (pt (fiber∙ (FiberSeqProj F))) ≡ pt X
isoForPuppe∙ F =
  J (λ Y p →
    Iso.fun (J (λ Y p → Iso (typ (fiber∙ (FiberSeqProj F))) (typ Y))
                idIso
                p)
    (pt (fiber∙ (FiberSeqProj F))) ≡ pt Y)
    (funExt⁻
       (cong (Iso.fun)
             (JRefl (λ Y p → Iso (typ (fiber∙ (FiberSeqProj F))) (typ Y))
                    idIso))
       (pt (fiber∙ (FiberSeqProj F))))
    λ i → fst ((FiberSeq.eqFib F) (~ i))

puppe : {X Y Z : Pointed ℓ} → FiberSeq X Y Z → FiberSeq (Ω Z) X Y
puppe {X = X} {Y = Y} {Z = Z} F =
  transport
  (λ i → FiberSeq (Ω Z) (fst (FiberSeq.eqFib F (~ i))) Y)
  (puppeFiberFiberCase (FiberSeqProj F))

-- needs tidying up
puppeProjFiberFiberCase : {B C : Pointed ℓ} (f : B →∙ C)
    → FiberSeqProj (puppeFiberFiberCase f) ≡ (fiberMap∙ f)
puppeProjFiberFiberCase f = transportRefl _

puppeProjEqFibIncl : {A B C : Pointed ℓ} (F : FiberSeq A B C)
    → FiberSeqProj (puppe F) ≡ FiberSeqIncl F
puppeProjEqFibIncl {A = A} {B = B} {C = C} F =
  J (λ Y p → FiberSeqProj (transport (λ i → FiberSeq (Ω C) (fst (p i)) B)
                                      (puppeFiberFiberCase (FiberSeqProj F)))
             ≡ (snd Y)) (cong (FiberSeqProj) (transportRefl _) ∙ puppeProjFiberFiberCase (FiberSeqProj F)) (λ i → FiberSeq.eqFib F (~ i))
