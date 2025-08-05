module FiberOrCofiberSequences.ShortExactSequence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

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

swapSymLeftIso : {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : x ≡ z)
  (r : z ≡ y) → Iso ((sym q) ∙ p ≡ r) (p ≡ q ∙ r)
swapSymLeftIso p q r =
  compIso (∙LeftIso ((sym q) ∙ p) r q)
  (compIso (invIso (lCancelIsoLeftLeft p (q ∙ r) (sym q)))
           (lUnitIsoLeft p (q ∙ r)))

swapSymLeftIso' : {A : Type ℓ} {x y : A} (p : x ≡ y) (q : x ≡ y)
  → Iso (p ≡ q) (refl ≡ (sym p) ∙ q)
swapSymLeftIso' p q =
  invIso
  (compIso symIso
  (compIso (swapSymLeftIso q p refl)
           (invIso (compIso symIso (rUnitIsoRight q p)))))

conjReflSymIso : {A : Type ℓ} {x y : A} (p : x ≡ x) (q : x ≡ y)
  → Iso ((sym q) ∙ (sym p) ∙ q ≡ refl) ((sym q) ∙ p ∙ q ≡ refl)
conjReflSymIso p q =
  compIso (swapSymLeftIso ((sym p) ∙ q) q refl)
  (compIso symIso
  (compIso (rUnitIsoLeft q ((sym p) ∙ q))
  (compIso symIso
  (compIso (swapSymLeftIso q p q)
  (compIso (swapSymLeftIso' q (p ∙ q)) symIso)))))

Auxiliary≡Iso : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  (pb : typ (Ω B))
  → Iso (sym (snd (FiberSeqProj F)) ∙
          cong (fst (FiberSeqProj F)) (sym pb) ∙
          snd (FiberSeqProj F) ≡ refl)
         (sym (snd (FiberSeqProj F)) ∙
          cong (fst (FiberSeqProj F)) pb ∙
          snd (FiberSeqProj F) ≡ refl)
Auxiliary≡Iso F pb =
  conjReflSymIso
  ( cong (fst (FiberSeqProj F)) pb)
  ( snd (FiberSeqProj F))

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
