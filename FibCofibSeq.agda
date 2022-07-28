{-# OPTIONS --experimental-lossy-unification #-}
module FibCofibSeq where

open import Cubical.Foundations.Everything

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.Unit
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Exact
open import Cubical.Algebra.Group.Instances.Unit
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.HITs.SetTruncation renaming (rec to setRec)
open import Cubical.HITs.Truncation
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.LES

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


--projections from a fiber sequence (projections from a cofiber sequence will
--also need to be defined
FiberSeqBase : {A B C : Pointed ℓ} → FiberSeq A B C → Pointed ℓ
FiberSeqBase {C = C} F = C

FiberSeqTotal : {A B C : Pointed ℓ} → FiberSeq A B C → Pointed ℓ
FiberSeqTotal {B = B} F = B

FiberSeqFiber : {A B C : Pointed ℓ} → FiberSeq A B C → Pointed ℓ
FiberSeqFiber {A = A} F = A

postulate
  FiberSeqIncl : {A B C : Pointed ℓ} (F : FiberSeq A B C)
    → (FiberSeqFiber F →∙ FiberSeqTotal F)

  FiberSeqProj : {A B C : Pointed ℓ} (F : FiberSeq A B C)
    → (FiberSeqTotal F →∙ FiberSeqBase F)

  FibsEqOfFibSeq : {A A' B C : Pointed ℓ} (F : FiberSeq A B C)
    (G : FiberSeq A' B C) → (FiberSeqProj F) ≡ (FiberSeqProj G)
    → (A , FiberSeqIncl F) ≡ (A' , FiberSeqIncl G)
  

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

Group≡→AbGroup≡ : (G H : AbGroup ℓ) → (AbGroup→Group G) ≡ (AbGroup→Group H)
  → G ≡ H
Group≡→AbGroup≡ G H p =
  equivFun (AbGroupPath G H) (transport (λ i → GroupEquiv (AbGroup→Group G) (p i)) idGroupEquiv)

AbGroup≡→Group≡ : (G H : Group ℓ)
  (cG : (x y : ⟨ G ⟩) → GroupStr._·_ (snd G) x y ≡ GroupStr._·_ (snd G) y x)
  (cH : (x y : ⟨ H ⟩) → GroupStr._·_ (snd H) x y ≡ GroupStr._·_ (snd H) y x)
  → Group→AbGroup G cG ≡ Group→AbGroup H cH
  → G ≡ H
AbGroup≡→Group≡ G H cG cH p = cong (AbGroup→Group) p

isLES : (V : ℕ → Group ℓ) → ((n : ℕ) → GroupHom (V (suc n)) (V n)) → Type ℓ
isLES V E =
  (n : ℕ) (x : ⟨ V (suc n) ⟩)
  → (isInIm (E (suc n)) x → isInKer (E n) x)
  × (isInKer (E n) x → isInIm (E (suc n)) x)

LES→isEquiv : (V : ℕ → Group ℓ) (E : (n : ℕ) → GroupHom (V (suc n)) (V n)) (L : isLES V E) (n : ℕ) → V n ≡ UnitGroup → V (suc (suc (suc n))) ≡ UnitGroup → isEquiv (fst (E (suc n)))
LES→isEquiv V E L n VnUn V3+nUn =
  SES→isEquiv (V3+nUn ⁻¹) (VnUn ⁻¹) (E (suc (suc n))) (E (suc n)) (E n)
  (λ x → snd (L (suc n) x)) λ x → snd (L n x)

LES→Equiv : (V : ℕ → Group ℓ) (E : (n : ℕ) → GroupHom (V (suc n)) (V n)) (L : isLES V E) (n : ℕ) → V n ≡ UnitGroup → V (suc (suc (suc n))) ≡ UnitGroup → GroupEquiv (V (suc (suc n))) (V (suc n))
fst (fst (LES→Equiv V E L n VnUn V3+nUn)) = fst (E (suc n))
snd (fst (LES→Equiv V E L n VnUn V3+nUn)) = LES→isEquiv V E L n VnUn V3+nUn
snd (LES→Equiv V E L n VnUn V3+nUn) = snd (E (suc n))

fiberSequence : {A B C : Pointed ℓ} → FiberSeq A B C → ℕ → Group ℓ
fiberSequence F = {!!}

fiberSequenceEdges : {A B C : Pointed ℓ} (F : FiberSeq A B C) (n : ℕ) → GroupHom (fiberSequence F (suc n)) (fiberSequence F n)
fiberSequenceEdges = {!!}

fiberSequenceIsLES : {A B C : Pointed ℓ} (F : FiberSeq A B C) → isLES (fiberSequence F) (fiberSequenceEdges F)
fiberSequenceIsLES = {!!}

fiberSequenceAbGroups : {A B C : Pointed ℓ} (F : FiberSeq A B C) (n : ℕ) →
  (x y : ⟨ fiberSequence F (suc (suc (suc n))) ⟩)
  → GroupStr._·_ (snd (fiberSequence F (suc (suc (suc n))))) x y
  ≡ GroupStr._·_ (snd (fiberSequence F (suc (suc (suc n))))) y x
fiberSequenceAbGroups = {!!}

4SequenceOfFiberSequence : {A B C : Pointed ℓ} (F : FiberSeq A B C) (n m : ℕ)
  → (fiberSequence F) m ≡ πGr n C
  → ((fiberSequence F) (suc m) ≡ πGr n B)
  ×  (((fiberSequence F) (suc (suc m)) ≡ πGr n A)
  ×  ((fiberSequence F) (suc (suc (suc m))) ≡ πGr (suc n) C))
4SequenceOfFiberSequence = {!!}

4SequenceOfFiberSequenceAb : {A B C : Pointed ℓ} (F : FiberSeq A B C) (n m : ℕ)
  → Group→AbGroup ((fiberSequence F) (suc (suc (suc m))))  (fiberSequenceAbGroups F m) ≡ πAb n C
  → (Group→AbGroup ((fiberSequence F) (suc (suc (suc (suc m))))) (fiberSequenceAbGroups F (suc m)) ≡ πAb n B)
  × ((Group→AbGroup ((fiberSequence F) (suc (suc (suc (suc (suc m)))))) (fiberSequenceAbGroups F (suc (suc m))) ≡ πAb n A)
  × (Group→AbGroup ((fiberSequence F) (suc (suc (suc (suc (suc (suc m))))))) (fiberSequenceAbGroups F (suc (suc (suc m)))) ≡ πAb (suc n) C))
4SequenceOfFiberSequenceAb = {!!}

4SequenceOfFiberSequence' : {A B C : Pointed ℓ} (F : FiberSeq A B C) (n m : ℕ)
  → (fiberSequence F) m ≡ πGr n B
  → ((fiberSequence F) (suc m) ≡ πGr n A)
  × (((fiberSequence F) (suc (suc m)) ≡ πGr (suc n) C)
  × ((fiberSequence F) (suc (suc (suc m))) ≡ πGr (suc n) B))
4SequenceOfFiberSequence' = {!!}

4SequenceOfFiberSequenceAb' : {A B C : Pointed ℓ} (F : FiberSeq A B C) (n m : ℕ)
  → Group→AbGroup ((fiberSequence F) (suc (suc (suc m)))) (fiberSequenceAbGroups F m) ≡ πAb n B
  → (Group→AbGroup ((fiberSequence F) (suc (suc (suc (suc m))))) (fiberSequenceAbGroups F (suc m)) ≡ πAb n A)
  × ((Group→AbGroup ((fiberSequence F) (suc (suc (suc (suc (suc m)))))) (fiberSequenceAbGroups F (suc (suc m))) ≡ πAb (suc n) C)
  × (Group→AbGroup ((fiberSequence F) (suc (suc (suc (suc (suc (suc m))))))) (fiberSequenceAbGroups F (suc (suc (suc m)))) ≡ πAb (suc n) B))
4SequenceOfFiberSequenceAb' = {!!}

4SequenceOfFiberSequence'' : {A B C : Pointed ℓ} (F : FiberSeq A B C) (n m : ℕ)
  → (fiberSequence F) m ≡ πGr n A
  → ((fiberSequence F) (suc m) ≡ πGr (suc n) C)
  × (((fiberSequence F) (suc (suc m)) ≡ πGr (suc n) B)
  × ((fiberSequence F) (suc (suc (suc m))) ≡ πGr (suc n) A))
4SequenceOfFiberSequence'' = {!!}

FirstTermOfFiberSequence : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  → (fiberSequence F) 0 ≡ πGr 0 C
FirstTermOfFiberSequence = {!!} 

πGrCAppearinSeq : {A B C : Pointed ℓ} (F : FiberSeq A B C) (n : ℕ)
  → Σ[ m ∈ ℕ ] (fiberSequence F) m ≡ πGr n C
πGrCAppearinSeq F zero = 0 , (FirstTermOfFiberSequence F)
πGrCAppearinSeq F (suc n) = (suc (suc (suc (fst (πGrCAppearinSeq F n)))))
  , snd (snd (4SequenceOfFiberSequence F n (fst (πGrCAppearinSeq F n))
    (snd (πGrCAppearinSeq F n))))

πAbCAppearinSeq : {A B C : Pointed ℓ} (F : FiberSeq A B C) (n : ℕ)
  →
  Σ[ m ∈ ℕ ] Group→AbGroup ((fiberSequence F) (suc (suc (suc m))))
                             (fiberSequenceAbGroups F m)
            ≡ πAb n C
πAbCAppearinSeq F n = fst (πGrCAppearinSeq F (suc n))
 , Group≡→AbGroup≡ {!!} {!!}
   ( snd (πGrCAppearinSeq F (suc n)))

πGrBAppearinSeq : {A B C : Pointed ℓ} (F : FiberSeq A B C) (n : ℕ)
  → Σ[ m ∈ ℕ ] (fiberSequence F) m ≡ πGr n B
πGrBAppearinSeq F n = (suc (fst (πGrCAppearinSeq F n)))
  , fst (4SequenceOfFiberSequence F n (fst (πGrCAppearinSeq F n))
    (snd (πGrCAppearinSeq F n)))

πAbBAppearinSeq : {A B C : Pointed ℓ} (F : FiberSeq A B C) (n : ℕ)
  →
  Σ[ m ∈ ℕ ] Group→AbGroup ((fiberSequence F) (suc (suc (suc m))))
                             (fiberSequenceAbGroups F m)
            ≡ πAb n B
πAbBAppearinSeq F n = {!!}

oneBackFromπAbBIsAb : {A B C : Pointed ℓ} (F : FiberSeq A B C) (n : ℕ)
  → (x y : ⟨ (fiberSequence F) (suc (suc (fst (πAbBAppearinSeq F n)))) ⟩)
  → ((GroupStr._·_
     ( snd ((fiberSequence F) (suc (suc (fst (πAbBAppearinSeq F n))))))) x y)
  ≡ (GroupStr._·_
    ( snd ((fiberSequence F) (suc (suc (fst (πAbBAppearinSeq F n)))))) y x)
oneBackFromπAbBIsAb F n = {!!}

πGrAAppearinSeq : {A B C : Pointed ℓ} (F : FiberSeq A B C) (n : ℕ)
  → Σ[ m ∈ ℕ ] (fiberSequence F) m ≡ πGr n A
πGrAAppearinSeq F n = (suc (suc (fst (πGrCAppearinSeq F n))))
  , fst (snd (4SequenceOfFiberSequence F n (fst (πGrCAppearinSeq F n))
    (snd (πGrCAppearinSeq F n))))

πAbAAppearinSeq : {A B C : Pointed ℓ} (F : FiberSeq A B C) (n : ℕ)
  → Σ[ m ∈ ℕ ] Group→AbGroup ((fiberSequence F) (suc (suc (suc m))))
                                (fiberSequenceAbGroups F m)
               ≡ πAb n A
πAbAAppearinSeq F n = {!!}

open πLES

ExactSequenceEquiv : (A B C : Pointed ℓ) (n : ℕ) → FiberSeq A B C
  → (AbGroupEquiv {ℓ} {ℓ} (πAb (suc n) C) UnitAbGroup)
  → (AbGroupEquiv {ℓ} {ℓ} (πAb n C) UnitAbGroup)
  → AbGroupEquiv (πAb n B) (πAb n A)
ExactSequenceEquiv A B C n F πn+1CIsUnit πnCIsUnit =
  transport
  (λ i → AbGroupEquiv
         ( snd (πAbBAppearinSeq F n) i)
         ( fst (4SequenceOfFiberSequenceAb' F n (fst (πAbBAppearinSeq F n))
                (snd (πAbBAppearinSeq F n))) i))
  (LES→Equiv
  ( fiberSequence F)
  ( fiberSequenceEdges F)
  ( fiberSequenceIsLES F)
  ( suc (suc (fst (πAbBAppearinSeq F n))))
  ( cong ( AbGroup→Group)
         ( {!!}
           ∙ equivFun (AbGroupPath (πAb n C) UnitAbGroup) πnCIsUnit))
  ( cong ( AbGroup→Group)
         ( fst (snd (4SequenceOfFiberSequenceAb' F
                    ( fst (πAbBAppearinSeq F n))
                    n (snd (πAbBAppearinSeq F n))))
           ∙ equivFun ( AbGroupPath (πAb (suc n) C) UnitAbGroup) πn+1CIsUnit)))
