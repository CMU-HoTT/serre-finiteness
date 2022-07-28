module FiberOrCofiberSequences.ShortExactSequence where

open import Cubical.Foundations.Everything

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation renaming (rec to propRec)
open import Cubical.HITs.SetTruncation renaming (elim to setElim)
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base

open import FiberOrCofiberSequences.Base
open import FiberOrCofiberSequences.PuppeLemma

private
  variable
    ℓ : Level

iteratedPuppeUniversalEquiv' : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  (pb : typ (Ω B))
  → (Σ[ pa ∈ typ (Ω A) ] sym (snd (FiberSeqIncl F))
      ∙ cong (fst (FiberSeqIncl F)) (sym pa) ∙ snd (FiberSeqIncl F) ≡ pb)
  ≃ (sym (snd (FiberSeqProj F)) ∙ cong (fst (FiberSeqProj F)) (sym pb)
     ∙ snd (FiberSeqProj F) ≡ refl {x = pt C})
iteratedPuppeUniversalEquiv' F =
  transport
  (λ i → (pb : typ (Ω (FiberSeqTotal F)))
   → (Σ[ pa ∈ typ (Ω (FiberSeqFiber F)) ] (twiceIteratedPuppeIncl F i pa) ≡ pb)
   ≃ ((twiceIteratedPuppeProj F i pb) ≡ refl {x = pt (FiberSeqBase F)}))
  (UniversalEquiv (puppe (puppe (puppe F))))

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

lUnitIsoLeft : {A : Type ℓ} {a b : A} (p q : a ≡ b)
  → Iso (refl ∙ p ≡ q) (p ≡ q)
lUnitIsoLeft p q = ∙IsoOnLeft (lUnit p)

lUnitIsoRight : {A : Type ℓ} {a b : A} (p q : a ≡ b)
  → Iso (p ≡ q) (p ≡ refl ∙ q)
lUnitIsoRight p q = ∙IsoOnRight (lUnit q)

rUnitIsoLeft : {A : Type ℓ} {a b : A} (p q : a ≡ b)
  → Iso (p ∙ refl ≡ q) (p ≡ q)
rUnitIsoLeft p q = ∙IsoOnLeft (rUnit p)

rUnitIsoRight : {A : Type ℓ} {a b : A} (p q : a ≡ b)
  → Iso (p ≡ q) (p ≡ q ∙ refl)
rUnitIsoRight p q = ∙IsoOnRight (rUnit q)

lCancelIsoLeftLeft : {A : Type ℓ} {a b c : A} (p p' : b ≡ c) (q : a ≡ b)
  → Iso (refl ∙ p ≡ p') ((sym q) ∙ q ∙ p ≡ p')
lCancelIsoLeftLeft p p' q = ∙IsoOnLeft (assoc _ _ _ ∙ cong (_∙ p) (lCancel q))

rCancelIsoLeftLeft : {A : Type ℓ} {a b c : A} (p p' : b ≡ c) (q : b ≡ a)
  → Iso (refl ∙ p ≡ p') (q ∙ (sym q) ∙ p ≡ p')
rCancelIsoLeftLeft p p' q = ∙IsoOnLeft (assoc _ _ _ ∙ cong (_∙ p) (rCancel q))

lCancelIsoRightLeft : {A : Type ℓ} {a b c : A} (p p' : a ≡ b) (q : c ≡ b)
  → Iso (p ∙ refl ≡ p') (p ∙ (sym q) ∙ q ≡ p')
lCancelIsoRightLeft p p' q = ∙IsoOnLeft (cong (p ∙_) (lCancel q))

rCancelIsoRightLeft : {A : Type ℓ} {a b c : A} (p p' : a ≡ b) (q : b ≡ c)
  → Iso (p ∙ refl ≡ p') (p ∙ q ∙ (sym q) ≡ p')
rCancelIsoRightLeft p p' q = ∙IsoOnLeft (cong (p ∙_) (rCancel q))

∙LeftIso : {A : Type ℓ} {a b c : A} (p p' : b ≡ c) (q : a ≡ b)
  → Iso (p ≡ p') (q ∙ p ≡ q ∙ p')
∙LeftIso p p' q = congPathIso (λ _ → isoToEquiv (∙IsoOnLeft q))

∙RightIso : {A : Type ℓ} {a b c : A} (p p' : a ≡ b) (q : b ≡ c)
  → Iso (p ≡ p') (p ∙ q ≡ p' ∙ q)
∙RightIso p p' q = congPathIso (λ _ → isoToEquiv (∙IsoOnRight q))

assocIsoLeft : {A : Type ℓ} {a b c d : A} (p : a ≡ b) (q : b ≡ c) (r : c ≡ d)
  (s : a ≡ d) → Iso ((p ∙ q) ∙ r ≡ s) (p ∙ q ∙ r ≡ s)
assocIsoLeft p q r s = ∙IsoOnLeft (assoc p q r)

Auxiliary≡Iso : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  (pb : typ (Ω B))
  → Iso (sym (snd (FiberSeqProj F)) ∙
          cong (fst (FiberSeqProj F)) (sym pb) ∙
          snd (FiberSeqProj F) ≡ refl)
         (sym (snd (FiberSeqProj F)) ∙
          cong (fst (FiberSeqProj F)) pb ∙
          snd (FiberSeqProj F) ≡ refl)
Auxiliary≡Iso F pb =
 compIso (∙LeftIso (sym (snd (FiberSeqProj F))
                    ∙ cong (fst (FiberSeqProj F)) (sym pb)
                    ∙ snd (FiberSeqProj F)) refl (snd (FiberSeqProj F)))
 (compIso (invIso (rUnitIsoRight (snd (FiberSeqProj F)
                         ∙ sym (snd (FiberSeqProj F))
                         ∙ cong (fst (FiberSeqProj F)) (sym pb)
                         ∙ snd (FiberSeqProj F)) (snd (FiberSeqProj F))))
 (compIso (invIso (rCancelIsoLeftLeft (cong (fst (FiberSeqProj F)) (sym pb)
                                       ∙ snd (FiberSeqProj F))
                                      (snd (FiberSeqProj F))
                                      (snd (FiberSeqProj F))))
 (compIso (lUnitIsoLeft (cong (fst (FiberSeqProj F)) (sym pb)
                        ∙ snd (FiberSeqProj F))
                        (snd (FiberSeqProj F)))
 (compIso (∙RightIso (cong (fst (FiberSeqProj F)) (sym pb)
                     ∙ snd (FiberSeqProj F)) (snd (FiberSeqProj F))
                     (sym (snd (FiberSeqProj F))))
 (compIso (assocIsoLeft (cong (fst (FiberSeqProj F)) (sym pb))
                        (snd (FiberSeqProj F))
                        (sym (snd (FiberSeqProj F)))
                        (snd (FiberSeqProj F)
                        ∙ sym (snd (FiberSeqProj F))))
 (compIso (invIso (rCancelIsoRightLeft (cong (fst (FiberSeqProj F)) (sym pb))
                                       (snd (FiberSeqProj F)
                                       ∙ sym (snd (FiberSeqProj F)))
                                       (snd (FiberSeqProj F))))
 (compIso (rUnitIsoLeft (cong (fst (FiberSeqProj F)) (sym pb))
                        (snd (FiberSeqProj F)
                        ∙ sym (snd (FiberSeqProj F))))
 (compIso symIso
 (compIso (invIso (lUnitIsoLeft (snd (FiberSeqProj F)
                                ∙ sym (snd (FiberSeqProj F)))
                                (cong (fst (FiberSeqProj F)) (sym pb))))
 (compIso (invIso (rCancelIsoRightLeft refl
                     (cong (fst (FiberSeqProj F)) (sym pb))
                     (snd (FiberSeqProj F))))
 (compIso (lUnitIsoLeft refl
                     (cong (fst (FiberSeqProj F)) (sym pb)))
 (compIso (∙LeftIso refl (cong (fst (FiberSeqProj F)) (sym pb))
                         (cong (fst (FiberSeqProj F)) pb))
 (compIso (rUnitIsoLeft (cong (fst (FiberSeqProj F)) pb)
                        (cong (fst (FiberSeqProj F)) pb
                        ∙ cong (fst (FiberSeqProj F)) (sym pb)))
 (compIso (∙LeftIso (cong (fst (FiberSeqProj F)) pb)
                    (cong (fst (FiberSeqProj F)) pb
                    ∙ cong (fst (FiberSeqProj F)) (sym pb))
                    (sym (snd (FiberSeqProj F))))
 (compIso symIso
 (compIso (invIso (rCancelIsoRightLeft (sym (snd (FiberSeqProj F)))
                                       (sym (snd (FiberSeqProj F))
                                       ∙ cong (fst (FiberSeqProj F)) pb)
                                       (cong (fst (FiberSeqProj F)) pb)))
 (compIso (rUnitIsoLeft (sym (snd (FiberSeqProj F)))
                        (sym (snd (FiberSeqProj F))
                        ∙ cong (fst (FiberSeqProj F)) pb))
 (compIso (∙RightIso (sym (snd (FiberSeqProj F)))
                     (sym (snd (FiberSeqProj F))
                     ∙ cong (fst (FiberSeqProj F)) pb)
                     (snd (FiberSeqProj F)))
 (compIso (∙RightIso (sym (snd (FiberSeqProj F))
                     ∙ snd (FiberSeqProj F))
                     (((sym (snd (FiberSeqProj F))
                      ∙ cong (fst (FiberSeqProj F)) pb)
                      ∙ snd (FiberSeqProj F)))
                     refl)
 (compIso (assocIsoLeft (sym (snd (FiberSeqProj F))) (snd (FiberSeqProj F)) refl
                        (((sym (snd (FiberSeqProj F))
                         ∙ cong (fst (FiberSeqProj F)) pb)
                         ∙ snd (FiberSeqProj F)) ∙ refl))
 (compIso (invIso (lCancelIsoLeftLeft refl
                      (((sym (snd (FiberSeqProj F))
                       ∙ cong (fst (FiberSeqProj F)) pb)
                       ∙ snd (FiberSeqProj F))
                       ∙ refl)
                    (snd (FiberSeqProj F))))
 (compIso (lUnitIsoLeft refl (((sym (snd (FiberSeqProj F))
                             ∙ cong (fst (FiberSeqProj F)) pb)
                             ∙ snd (FiberSeqProj F))
                             ∙ refl))
 (compIso symIso
 (compIso (rUnitIsoLeft ((sym (snd (FiberSeqProj F))
                         ∙ cong (fst (FiberSeqProj F)) pb)
                         ∙ snd (FiberSeqProj F))
                        refl)
 (assocIsoLeft (sym (snd (FiberSeqProj F))) (cong (fst (FiberSeqProj F)) pb)
               (snd (FiberSeqProj F)) refl)))))))))))))))))))))))))

iteratedPuppeUniversalEquiv : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  (pb : typ (Ω B))
  → (Σ[ pa ∈ typ (Ω A) ] sym (snd (FiberSeqIncl F))
      ∙ cong (fst (FiberSeqIncl F)) pa ∙ snd (FiberSeqIncl F) ≡ pb)
  ≃ (sym (snd (FiberSeqProj F)) ∙ cong (fst (FiberSeqProj F)) pb
     ∙ snd (FiberSeqProj F) ≡ refl {x = pt C})
iteratedPuppeUniversalEquiv F pb =
  invEquiv (Σ-cong-equiv-fst (isoToEquiv symIso))
  ∙ₑ iteratedPuppeUniversalEquiv' F pb
  ∙ₑ isoToEquiv (Auxiliary≡Iso F pb)

FiberSeq→ExactFstRecCase : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  → (pb : typ (Ω B))
  → (pa : typ (Ω A))
  → ∥ sym (snd (FiberSeqIncl F)) ∙ cong (fst (FiberSeqIncl F)) pa
       ∙ snd (FiberSeqIncl F) ≡ pb ∥₁
  → isInKer (πHom 0 (FiberSeqProj F)) ∣ pb ∣₂
FiberSeq→ExactFstRecCase F pb pa = propRec
 (isOfHLevelPath' 1 isSetSetTrunc (πFun 0 (FiberSeqProj F) ∣ pb ∣₂) ∣ refl ∣₂)
 λ q → Iso.inv PathIdTrunc₀Iso
 ∣ doubleCompPath-elim' (sym (snd (FiberSeqProj F)))
                       (cong (fst (FiberSeqProj F)) pb)
                       (snd (FiberSeqProj F)) ∙
  equivFun (iteratedPuppeUniversalEquiv F pb) (pa , q) ∣₁

FiberSeq→ExactFstRecCase'' : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  → (pb : typ (Ω B))
  → (g : typ (πGr 0 A))
  → πFun 0 (FiberSeqIncl F) g ≡ ∣ pb ∣₂
  → isInKer (πHom 0 (FiberSeqProj F)) ∣ pb ∣₂
FiberSeq→ExactFstRecCase'' F pb =
  setElim
  (λ g → isSet→
  (isOfHLevelPath 2 isSetSetTrunc (πFun 0 (FiberSeqProj F) ∣ pb ∣₂) ∣ refl ∣₂))
  λ pa q → FiberSeq→ExactFstRecCase F pb pa
  (Iso.fun PathIdTrunc₀Iso
  (cong ∣_∣₂
  (doubleCompPath-elim' (sym (snd (FiberSeqIncl F)))
                        (cong (fst (FiberSeqIncl F)) pa)
                        (snd (FiberSeqIncl F)) ⁻¹) ∙ q))

FiberSeq→ExactFst : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  → (pb : typ (Ω B))
  → Σ[ g ∈ typ (πGr 0 A) ] πFun 0 (FiberSeqIncl F) g ≡ ∣ pb ∣₂
  → isInKer (πHom 0 (FiberSeqProj F)) ∣ pb ∣₂
FiberSeq→ExactFst F pb (g , q) = FiberSeq→ExactFstRecCase'' F pb g q

FiberSeq→ExactSndRecCase : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  → (pb : typ (Ω B))
  → ∥ sym (snd (FiberSeqProj F)) ∙ cong (fst (FiberSeqProj F)) pb
     ∙ snd (FiberSeqProj F) ≡ refl {x = pt C} ∥₁
  → isInIm (πHom 0 (FiberSeqIncl F)) ∣ pb ∣₂
FiberSeq→ExactSndRecCase F pb = propRec isPropPropTrunc
  λ q → ∣ ∣ fst (invEq (iteratedPuppeUniversalEquiv F pb) q) ∣₂ ,
          Iso.inv PathIdTrunc₀Iso
          ∣ doubleCompPath-elim' (sym (snd (FiberSeqIncl F)))
                                 (cong (fst (FiberSeqIncl F)) _)
                                 (snd (FiberSeqIncl F)) ∙
           snd (invEq (iteratedPuppeUniversalEquiv F pb) q) ∣₁ ∣₁

FiberSeq→ExactSnd : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  → (pb : typ (Ω B))
  → isInKer (πHom 0 (FiberSeqProj F)) ∣ pb ∣₂
  → isInIm (πHom 0 (FiberSeqIncl F)) ∣ pb ∣₂
FiberSeq→ExactSnd F pb q = FiberSeq→ExactSndRecCase F pb
  (Iso.fun PathIdTrunc₀Iso (cong ∣_∣₂ ((doubleCompPath-elim' (sym (snd (FiberSeqProj F))) (cong (fst (FiberSeqProj F)) pb) (snd (FiberSeqProj F))) ⁻¹) ∙ q))


FiberSeq→Exact : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  → ((x : ⟨ πGr 0 B ⟩)
  → (isInIm (πHom 0 (FiberSeqIncl F)) x → isInKer (πHom 0 (FiberSeqProj F)) x)
  × (isInKer (πHom 0 (FiberSeqProj F)) x → isInIm (πHom 0 (FiberSeqIncl F)) x))
FiberSeq→Exact {B = B} {C = C} F = setElim
 (λ x → isSet×
 (isSet→ (isOfHLevelPath 2 isSetSetTrunc (πFun 0 (FiberSeqProj F) x) ∣ refl ∣₂))
 (isSet→ (isProp→isSet isPropPropTrunc)))
 λ pb → propRec
 (isOfHLevelPath' 1 isSetSetTrunc (πFun 0 (FiberSeqProj F) ∣ pb ∣₂) ∣ refl ∣₂)
 (FiberSeq→ExactFst F pb) , (FiberSeq→ExactSnd F pb)

