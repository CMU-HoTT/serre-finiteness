module FiberOrCofiberSequences.Base where

open import Cubical.Foundations.Everything

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation renaming (rec to propRec)
open import Cubical.HITs.SetTruncation renaming (elim to setElim)
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.LES

open import PointedHITs

open import ConnectedCovers.TruncationLevelFacts

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

  FiberSeq : Pointed ℓ → Pointed ℓ → Pointed ℓ → Type ℓ
  -- likewise

--projections from a fiber sequence (projections from a cofiber sequence will
--also need to be defined
FiberSeqBase : {A B C : Pointed ℓ} → FiberSeq A B C → Pointed ℓ
FiberSeqBase {C = C} F = C

FiberSeqTotal : {A B C : Pointed ℓ} → FiberSeq A B C → Pointed ℓ
FiberSeqTotal {B = B} F = B

FiberSeqFiber : {A B C : Pointed ℓ} → FiberSeq A B C → Pointed ℓ
FiberSeqFiber {A = A} F = A

fiber∙ : {A B : Pointed ℓ} → (A →∙ B) → Pointed ℓ
fiber∙ {A = A} {B = B} f = fiber (fst f) (pt B) , (pt A) , (snd f)

postulate
  FiberFiberSeq : {A B : Pointed ℓ} (f : A →∙ B)
    → FiberSeq (fiber∙ f) A B

  FiberSeqIncl : {A B C : Pointed ℓ} (F : FiberSeq A B C)
    → (FiberSeqFiber F →∙ FiberSeqTotal F)

  FiberSeqProj : {A B C : Pointed ℓ} (F : FiberSeq A B C)
    → (FiberSeqTotal F →∙ FiberSeqBase F)

  FiberSeqCompEq : {A B C : Pointed ℓ} (F : FiberSeq A B C)
    → (FiberSeqProj F ∘∙ FiberSeqIncl F) ≡ const∙ _ _

  EqOfEqFiberSeqProj : {A B C : Pointed ℓ} (F G : FiberSeq A B C)
    → (FiberSeqProj F) ≡ (FiberSeqProj G) → F ≡ G

Cone : {A B : Pointed ℓ} (f : A →∙ B) → Pointed ℓ → Type ℓ
Cone {A = A} {B = B} f A' = Σ[ h ∈ A' →∙ A ] f ∘∙ h ≡ const∙ A' B

Fun→Cone→Cone : {A B : Pointed ℓ} (f : A →∙ B) (A' B' : Pointed ℓ)
  → Cone f B' → (A' →∙ B') → Cone f A'
Fun→Cone→Cone f A' B' (h , p) g =
  (h ∘∙ g) , (∘∙-assoc f h g) ⁻¹ ∙ cong (_∘∙ g) p ∙ ΣPathP (refl , (lUnit _ ⁻¹))

FiberSeqCone : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  → Cone (FiberSeqProj F) A
FiberSeqCone F = FiberSeqIncl F , FiberSeqCompEq F

postulate
  FiberSeqUniversalProperty : {A B C : Pointed ℓ} (F : FiberSeq A B C)
    → (A' : Pointed ℓ) → isEquiv (Fun→Cone→Cone (FiberSeqProj F) A' A
                                   (FiberSeqCone F))

  UniversalEquiv : {A B C : Pointed ℓ} (F : FiberSeq A B C) (b : typ B)
    → (Σ[ a ∈ typ A ] fst (FiberSeqIncl F) a ≡ b)
     ≃ (fst (FiberSeqProj F) b ≡ pt C)

FiberSeqCompEq' : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  → Σ[ p ∈ fst (FiberSeqProj F) ∘ fst (FiberSeqIncl F) ≡ (λ _ → snd C) ]
     PathP (λ i → p i (snd (FiberSeqFiber F)) ≡ snd (FiberSeqBase F))
           (cong (fst (FiberSeqProj F)) (snd (FiberSeqIncl F))
            ∙ snd (FiberSeqProj F)) refl
FiberSeqCompEq' F = PathPΣ (FiberSeqCompEq F)

FiberSeqCompEq'' : {A B C  : Pointed ℓ} (F : FiberSeq A B C)
  → Σ[ p ∈ fst (FiberSeqProj F) ∘ fst (FiberSeqIncl F) ≡ (λ _ → snd C) ]
     transport (λ i → p i (snd (FiberSeqFiber F)) ≡ snd (FiberSeqBase F))
     (cong (fst (FiberSeqProj F)) (snd (FiberSeqIncl F))
      ∙ snd (FiberSeqProj F)) ≡ refl
FiberSeqCompEq'' F = (fst (FiberSeqCompEq' F)) , (fromPathP (snd (FiberSeqCompEq' F)))

-- these transportPathLemmas should be renamed and moved elsewhere
transportPathLemma' : {A : Type ℓ} {a b c : A} (p : a ≡ b) (q : b ≡ c)
  → transp (λ i → p (~ i) ≡ c) i0 q ≡ p ∙ q
transportPathLemma' {c = c} =
  J (λ b' p' → (q : b' ≡ c) → transp (λ i → p' (~ i) ≡ c) i0 q ≡ p' ∙ q)
    λ q → transportRefl q ∙ lUnit q

transportPathLemmaRight : {A : Type ℓ} {a b c : A} (p : b ≡ c) (q : a ≡ b)
  → transport (λ i → a ≡ (p i)) q ≡ q ∙ p
transportPathLemmaRight {a = a} {b = b} =
  J (λ c p → ∀ (q : a ≡ b) → transport (λ i → a ≡ (p i)) q ≡ q ∙ p)
    λ q → fromPathP (rUnit q)

transportPathLemmaLeft : {A : Type ℓ} {a b c : A} (p : b ≡ a) (q : b ≡ c)
  → transport (λ i → p i ≡ c) q ≡ (p ⁻¹) ∙ q
transportPathLemmaLeft {b = b} {c = c} =
  J (λ a p → (q : b ≡ c) → transport (λ i → p i ≡ c) q ≡ (p ⁻¹) ∙ q)
    (λ q → fromPathP (lUnit q ∙ cong (_∙ q) symRefl))

transportFunPathLemma'' : {A : Type ℓ} (a a' : A) (p : a ≡ a')
  → transp (λ i → p (~ i) ≡ a') i0 refl ≡ p
transportFunPathLemma'' a a' =
  J (λ a'' p → transp (λ i → p (~ i) ≡ a'') i0 refl ≡ p)
    (transportRefl refl)

transportFunPathLemma' : {A B : Type ℓ} {a a' : A} {b : B} (f : A → B)
  (q : a ≡ a') (r : f a' ≡ b)
  → transport (λ i → f (q (~ i)) ≡ b) r ≡ cong f q ∙ r
transportFunPathLemma' {b = b} f =
  J ( λ a* q
        → (r : f a* ≡ b)
        → transport (λ i → f (q (~ i)) ≡ b) r ≡ cong f q ∙ r)
    ( λ r → transportRefl r ∙ lUnit r)

transportFunPathLemma : {A B : Type ℓ} (a : A) (b : B) (f g : A → B)
  (p : f ≡ g) (q : f a ≡ b) (r : g a ≡ b)
  → transport (λ i → p i a ≡ b) q ≡ r
  → (λ i → p i a) ⁻¹ ∙ q ≡ r
transportFunPathLemma a b f g =
  J ( λ h p
       → (q : f a ≡ b) (r : h a ≡ b)
       → transport (λ i → p i a ≡ b) q ≡ r
       → (λ i → p i a) ⁻¹ ∙ q ≡ r)
    ( λ q r s → cong (_∙ q) (symRefl ⁻¹)
                 ∙ lUnit q ⁻¹
                 ∙ (s ⁻¹ ∙ transportRefl q) ⁻¹)

movingTransportPathLemma : (A : Type ℓ) (a b : A)
  (p : a ≡ b) (q : a ≡ b) (r : a ≡ a)
  → transport (λ i → p i ≡ q i) r ≡ p ⁻¹ ∙ r ∙ q
movingTransportPathLemma A a b =
  J (λ b' p → ∀ (q : a ≡ b') (r : a ≡ a)
    → transport (λ i → p i ≡ q i) r ≡ p ⁻¹ ∙ r ∙ q)
    λ q r → transportPathLemmaRight q r ∙ lUnit _ ∙ cong (_∙ r ∙ q) symRefl

movFunTransportPathLemma : {A B : Type ℓ} {a : A} {b c : B} (f : B → A)
  (p : b ≡ c) (q : a ≡ a) (r : f b ≡ a)
  → transport (λ i → q i ≡ f (p i)) (r ⁻¹) ≡ q ⁻¹ ∙ (r ⁻¹) ∙ (cong f p)
movFunTransportPathLemma {a = a} {b = b} f =
 J (λ c p → ∀ (q : a ≡ a) (r : f b ≡ a)
          → transport (λ i → q i ≡
                              f (p i)) (r ⁻¹) ≡ q ⁻¹ ∙ (r ⁻¹) ∙ (cong f p))
   λ q r → transportPathLemmaLeft q (r ⁻¹) ∙ rUnit (q ⁻¹ ∙ r ⁻¹)
                                            ∙ (assoc (q ⁻¹) (r ⁻¹) refl) ⁻¹

FiberSeqCompEq''' : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  → Σ[ p ∈ fst (FiberSeqProj F) ∘ fst (FiberSeqIncl F) ≡ (λ _ → snd C) ]
     (λ i → p i (snd A)) ⁻¹
     ∙ (cong (fst (FiberSeqProj F)) (snd (FiberSeqIncl F)))
     ∙ (snd (FiberSeqProj F))
     ≡ refl
FiberSeqCompEq''' F = (fst (FiberSeqCompEq' F)) ,
  transportFunPathLemma (snd (FiberSeqFiber F)) (snd (FiberSeqBase F))
  (fst (FiberSeqProj F) ∘ fst (FiberSeqIncl F))
  (λ _ → snd (FiberSeqBase F))
  (fst (FiberSeqCompEq' F))
  ((cong (fst (FiberSeqProj F)) (snd (FiberSeqIncl F)))
  ∙ (snd (FiberSeqProj F)))
  refl
  (snd (FiberSeqCompEq'' F))
  

congFunPathLemma : {A B : Type ℓ} {a a' : A} (p : a ≡ a') (f g : A → B)
  (q : f ≡ g) → (λ i → q i a) ∙ cong g p ∙ (sym (λ i → q i a')) ≡ cong f p
congFunPathLemma {a = a} {a' = a'} p f g =
  J (λ h q → (λ i → q i a) ∙ cong h p ∙ (sym (λ i → q i a')) ≡ cong f p)
  (lUnit _ ⁻¹ ∙ cong ((cong f p) ∙_) (symRefl ⁻¹) ∙ rUnit _ ⁻¹)

congConstIsRefl : {A B : Type ℓ} {a a' : A} {b : B} (p : a ≡ a')
  → cong (λ _ → b) p ≡ refl
congConstIsRefl p = refl

postulate
  FibsEqOfFibSeq : {A A' B C : Pointed ℓ} (F : FiberSeq A B C)
    (G : FiberSeq A' B C) → (FiberSeqProj F) ≡ (FiberSeqProj G)
    → (A , FiberSeqIncl F) ≡ (A' , FiberSeqIncl G)

  FibsIsoOfFibSeq : {A A' B C : Pointed ℓ} (F : FiberSeq A B C)
    (G : FiberSeq A' B C) → (FiberSeqProj F) ≡ (FiberSeqProj G)
    → Σ[ pr ∈ Σ[ H ∈ Iso (typ A) (typ A') ] Iso.fun H (pt A) ≡ pt A' ]
       (FiberSeqIncl F
       ∘∙ ((Iso.inv (fst pr)) , cong (Iso.inv (fst pr)) (sym (snd pr))
                                ∙ Iso.leftInv (fst pr) _))
     ≡ FiberSeqIncl G
    
    

  ProjOfFiberFiberSeq : {A B : Pointed ℓ} (f : A →∙ B)
    → FiberSeqProj (FiberFiberSeq f) ≡ f

inclOfFiberFiberSeq : {A B : Pointed ℓ} (f : A →∙ B)
  → ((fiber∙ f) →∙ A)
inclOfFiberFiberSeq f = fst , refl

postulate
  InclOfFiberFiberSeq : {A B : Pointed ℓ} (f : A →∙ B)
    → FiberSeqIncl (FiberFiberSeq f) ≡ (fst , refl {x = snd A})


FibsEqOfFibSeq' : {A A' B C : Pointed ℓ} (F : FiberSeq A B C)
  (G : FiberSeq A' B C) → (FiberSeqProj F) ≡ (FiberSeqProj G)
  →
  Σ[ p ∈ A ≡ A' ] PathP (λ i → (p i) →∙ B) (FiberSeqIncl F) (FiberSeqIncl G)
FibsEqOfFibSeq' F G q = PathPΣ (FibsEqOfFibSeq F G q)

FibsEqFiberFiberSeq : {A B C : Pointed ℓ} (F : FiberSeq A B C) →
  Σ[ p ∈ A ≡ fiber∙ (FiberSeqProj F) ]
   PathP (λ i → (p i) →∙ B) (FiberSeqIncl F) (fst , refl)
FibsEqFiberFiberSeq {A = A} {B = B} {C = C} F =
  transport
  ( λ i → Σ[ p ∈ A ≡ fiber∙ (FiberSeqProj F) ]
            PathP
            ( λ i → (p i) →∙ B)
            ( FiberSeqIncl F)
            ( InclOfFiberFiberSeq (FiberSeqProj F) i))
  ( FibsEqOfFibSeq' F (FiberFiberSeq (FiberSeqProj F))
  ( ProjOfFiberFiberSeq (FiberSeqProj F) ⁻¹))

FibsIsoFiberFiberSeq : {A B C : Pointed ℓ} (F : FiberSeq A B C) →
  Σ[ H ∈ Iso (typ (fiber∙ (FiberSeqProj F))) (typ A) ]
  Iso.fun H (pt (fiber∙ (FiberSeqProj F))) ≡ (pt A)
FibsIsoFiberFiberSeq F =
  fst (FibsIsoOfFibSeq
       ( FiberFiberSeq
         ( FiberSeqProj F))
       ( F)
       ( ProjOfFiberFiberSeq _))

postulate  
  BaseEqFiberSeq : {A B C C' : Pointed ℓ} → C ≡ C' → FiberSeq A B C 
    → FiberSeq A B C'

  BaseEquivFiberSeq : {A B C C' : Pointed ℓ} → C ≃∙ C' → FiberSeq A B C
    → FiberSeq A B C'

  BaseIsoFiberSeq : {A B C C' : Pointed ℓ} (H : Iso (typ C) (typ C'))
    → Iso.fun H (pt C) ≡ pt C' → FiberSeq A B C → FiberSeq A B C'

  BaseIsoFiberSeqProj : {A B C C' : Pointed ℓ} (H : Iso (typ C) (typ C'))
    (p : Iso.fun H (pt C) ≡ pt C') (F : FiberSeq A B C)
    → FiberSeqProj (BaseIsoFiberSeq H p F)
    ≡ (Iso.fun H , p) ∘∙ FiberSeqProj F

  BaseIsoFiberSeqIncl : {A B C C' : Pointed ℓ} (H : Iso (typ C) (typ C'))
    (p : Iso.fun H (pt C) ≡ pt C') (F : FiberSeq A B C)
    → FiberSeqIncl (BaseIsoFiberSeq H p F)
    ≡ FiberSeqIncl F

  TotalEqFiberSeq : {A B B' C : Pointed ℓ} → B ≡ B' → FiberSeq A B C
    → FiberSeq A B' C

  TotalEquivFiberSeq : {A B B' C : Pointed ℓ} → B ≃∙ B' → FiberSeq A B C
    → FiberSeq A B' C

  TotalIsoFiberSeq : {A B B' C : Pointed ℓ} (H : Iso (typ B) (typ B'))
    → Iso.fun H (pt B) ≡ pt B' → FiberSeq A B C → FiberSeq A B' C

  TotalIsoFiberSeqProj : {A B B' C : Pointed ℓ} (H : Iso (typ B) (typ B'))
    (p : Iso.fun H (pt B) ≡ pt B') (F : FiberSeq A B C)
    → FiberSeqProj (TotalIsoFiberSeq H p F)
    ≡ (FiberSeqProj F) ∘∙ (Iso.inv H , cong (Iso.inv H) (sym p)
                                       ∙ Iso.leftInv H _)

  TotalIsoFiberSeqIncl : {A B B' C : Pointed ℓ} (H : Iso (typ B) (typ B'))
    (p : Iso.fun H (pt B) ≡ pt B') (F : FiberSeq A B C)
    → FiberSeqIncl (TotalIsoFiberSeq H p F)
    ≡ (Iso.fun H , p) ∘∙ (FiberSeqIncl F)

  FiberEqFiberSeq : {A A' B C : Pointed ℓ} → A ≡ A' → FiberSeq A B C
    → FiberSeq A' B C

  FiberEquivFiberSeq : {A A' B C : Pointed ℓ} → A ≃∙ A' → FiberSeq A B C
    → FiberSeq A' B C

  FiberIsoFiberSeq : {A A' B C : Pointed ℓ} (H : Iso (typ A) (typ A'))
    → Iso.fun H (pt A) ≡ pt A' → FiberSeq A B C → FiberSeq A' B C

  FiberIsoFiberSeqProj : {A A' B C : Pointed ℓ} (H : Iso (typ A) (typ A'))
    (p : Iso.fun H (pt A) ≡ pt A') (F : FiberSeq A B C)
    → FiberSeqProj (FiberIsoFiberSeq H p F)
    ≡ FiberSeqProj F

  FiberIsoFiberSeqIncl : {A A' B C : Pointed ℓ} (H : Iso (typ A) (typ A'))
    (p : Iso.fun H (pt A) ≡ pt A') (F : FiberSeq A B C)
    → FiberSeqIncl (FiberIsoFiberSeq H p F)
    ≡ (FiberSeqIncl F) ∘∙ (Iso.inv H , cong (Iso.inv H) (sym p)
                                       ∙ Iso.leftInv H (pt A))
     
  ContrBase→TotalEqFib : {A B C : Pointed ℓ} → isContr (typ C)
    → FiberSeq A B C → A ≡ B


