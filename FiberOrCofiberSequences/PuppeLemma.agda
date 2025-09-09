{-# OPTIONS --lossy-unification #-}
module FiberOrCofiberSequences.PuppeLemma where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Homotopy.Loopspace

open import PointedHITs

open import FiberOrCofiberSequences.Base
open import FiberOrCofiberSequences.CofiberBase

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

postulate
  fiberΩ-comm : {B C : Pointed ℓ} (f : B →∙ C)
    → Iso (typ (Ω (fiber∙ f))) (typ (fiber∙ (Ω→ f)))

puppeTotalIso : {B C : Pointed ℓ} (f : B →∙ C) →
  Σ[ H ∈ Iso (typ (fiber∙ (inclOfFiberFiberSeq f))) (typ (Ω C)) ]
  Iso.fun H  (pt (fiber∙ (inclOfFiberFiberSeq f))) ≡ (pt (Ω C))
Iso.fun (fst (puppeTotalIso f)) ((b' , q) , p) = (snd f) ⁻¹ ∙ cong (fst f) (p ⁻¹) ∙ q
Iso.inv (fst (puppeTotalIso {B = B} f)) p = (pt B , snd f ∙ p) , refl
Iso.rightInv (fst (puppeTotalIso f)) p = cong (snd f ⁻¹ ∙_) (lUnit (snd f ∙ p) ⁻¹) ∙ assoc (snd f ⁻¹) (snd f) p ∙ cong (_∙ p) (lCancel (snd f)) ∙ lUnit p ⁻¹
Iso.leftInv (fst (puppeTotalIso f)) ((b' , q) , p) =
  ΣPathP ((ΣPathP (p ⁻¹ , toPathP (transportPathLemmaLeft (cong (fst f) (p ⁻¹)) (snd f ∙ Iso.fun (fst (puppeTotalIso f)) ((b' , q) , p)) ∙ cong (cong (fst f) (p ⁻¹) ⁻¹ ∙_) (assoc (snd f) (snd f ⁻¹) (cong (fst f) (p ⁻¹) ∙ q) ∙ cong (_∙ (cong (fst f) (p ⁻¹) ∙ q)) (rCancel (snd f))) ∙ cong (cong (fst f) (p ⁻¹) ⁻¹ ∙_) (lUnit (cong (fst f) (p ⁻¹) ∙ q) ⁻¹) ∙ assoc (cong (fst f) (p ⁻¹) ⁻¹) (cong (fst f) (p ⁻¹)) q ∙ cong (_∙ q) (lCancel (cong (fst f) (p ⁻¹))) ∙ lUnit q ⁻¹))) , toPathP (transportPathLemmaLeft (p ⁻¹) refl ∙ rUnit p ⁻¹))
snd (puppeTotalIso f) = cong (snd f ⁻¹ ∙_) (lUnit _ ⁻¹) ∙ lCancel (snd f)

{-puppeFiberIso2 : (B C : Pointed ℓ) (f : B →∙ C) →
  Iso (typ (fiber∙ (inclOfFiberFiberSeq (inclOfFiberFiberSeq f))))
     (Σ[ pr ∈ Σ[ b ∈ (typ B) ] (fst f) b ≡ pt C ]
      ((fst pr ≡ pt B) × (pr ≡ (pt B , snd f))))
Iso.fun (puppeFiberIso2 B C f) (((b , p) , q) , r) = (b , p) , (q , r)
Iso.inv (puppeFiberIso2 B C f) ((b , p) , (q , r)) = ((b , p) , q) , r
Iso.rightInv (puppeFiberIso2 B C f) qdr = refl
Iso.leftInv (puppeFiberIso2 B C f) qdr = refl

puppeFiberIso1 : (B C : Pointed ℓ) (f : B →∙ C) →
  Iso (Σ[ pr ∈ Σ[ b ∈ (typ B) ] (fst f) b ≡ pt C ]
       ((fst pr ≡ pt B) × (pr ≡ (pt B , snd f))))
      (typ (Ω B))
Iso.fun (puppeFiberIso1 B C f) ((b , p) , (q , r)) =
  (λ i →  fst (r (~ i))) ∙ q
Iso.inv (puppeFiberIso1 B C f) p = ((pt B) , (snd f)) , p , refl
Iso.rightInv (puppeFiberIso1 B C f) p = lUnit p ⁻¹
Iso.leftInv (puppeFiberIso1 B C f) ((b , p) , (q , r)) =
  ΣPathP
  ( (sym r)
  , ( toPathP
      ( ≡-×
        ( transportPathLemma'
          ( λ i → fst (r i)) _
        ∙ assoc
          ( λ i → fst (r i))
          ( λ i → fst (r (~ i)))
          ( q)
        ∙ cong
          ( _∙ q)
          ( rCancel (λ i → fst (r i)))
        ∙ lUnit q ⁻¹)
        ( transportFunPathLemma'' (b , p) (pt B , snd f) r))))

puppeFiberIso : {B C : Pointed ℓ} (f : B →∙ C) →
  Σ[ H ∈ Iso (typ (fiber∙ (inclOfFiberFiberSeq (inclOfFiberFiberSeq f))))
             (typ (Ω B)) ]
  Iso.fun H (pt (fiber∙ (inclOfFiberFiberSeq (inclOfFiberFiberSeq f))))
  ≡ (pt (Ω B))
puppeFiberIso = {!!}-}

postulate
  copuppe : {A B C : Pointed ℓ} → CofiberSeq A B C → CofiberSeq B C (S∙ A)

puppeFiberFiberCase : {B C : Pointed ℓ} (f : B →∙ C)
  → FiberSeq (Ω C) (fiber∙ f) B
puppeFiberFiberCase {B = B} {C = C} f =
  FiberIsoFiberSeq
  ( fst (puppeTotalIso f))
  ( snd (puppeTotalIso f))
  ( FiberFiberSeq
    ( inclOfFiberFiberSeq f))

puppe : {X Y Z : Pointed ℓ} → FiberSeq X Y Z → FiberSeq (Ω Z) X Y
puppe F = TotalIsoFiberSeq
          ( fst (FibsIsoFiberFiberSeq F))
          ( snd (FibsIsoFiberFiberSeq F))
          ( puppeFiberFiberCase
            ( FiberSeqProj F))

-- needs tidying up
puppeProjFiberFiberCase : {B C : Pointed ℓ} (f : B →∙ C)
    → FiberSeqProj (puppeFiberFiberCase f) ≡ (fiberMap∙ f)
puppeProjFiberFiberCase f = transportRefl _

postulate

  puppeProjEqFibIncl : {A B C : Pointed ℓ} (F : FiberSeq A B C)
    → FiberSeqProj (puppe F) ≡ FiberSeqIncl F

--puppeProjEqFibIncl F = {!!}
  {-( TotalIsoFiberSeqProj
    ( fst (FibsIsoFiberFiberSeq F))
    ( snd (FibsIsoFiberFiberSeq F))
    ( puppeFiberFiberCase (FiberSeqProj F))
  ∙ cong
    ( _∘∙ ( Iso.inv (fst (FibsIsoFiberFiberSeq F))
          , ( cong
              ( Iso.inv (fst (FibsIsoFiberFiberSeq F)))
              ( sym (snd (FibsIsoFiberFiberSeq F)))
            ∙ Iso.leftInv
              ( fst (FibsIsoFiberFiberSeq F))
              ( pt (fiber∙ (FiberSeqProj F))))))
    ( ( FiberIsoFiberSeqProj
        ( fst (puppeTotalIso (FiberSeqProj F)))
        ( snd (puppeTotalIso (FiberSeqProj F)))
        ( FiberFiberSeq
          ( inclOfFiberFiberSeq (FiberSeqProj F))))
      ∙ ProjOfFiberFiberSeq
        ( inclOfFiberFiberSeq (FiberSeqProj F))
      ∙ sym (InclOfFiberFiberSeq (FiberSeqProj F)))
  ∙ snd (FibsIsoOfFibSeq
         ( FiberFiberSeq
           ( FiberSeqProj F))
         ( F)
         ( ProjOfFiberFiberSeq
           ( FiberSeqProj F))))-}

{-alternativeIteratedPuppeFiberFiberCase : {B C : Pointed ℓ} (f : B →∙ C)
  → FiberSeq (Ω B) (Ω C) (fiber∙ f)
alternativeIteratedPuppeFiberFiberCase f =
  FiberIsoFiberSeq
  ( fst (puppeFiberIso f))
  ( snd (puppeFiberIso f))
  ( TotalIsoFiberSeq
    ( fst (puppeTotalIso f))
    ( snd (puppeTotalIso f))
    ( FiberFiberSeq
      ( inclOfFiberFiberSeq
        ( inclOfFiberFiberSeq f))))

alternativeIteratedPuppe : {A B C : Pointed ℓ} → FiberSeq A B C
  → FiberSeq (Ω B) (Ω C) A
alternativeIteratedPuppe F =
  BaseIsoFiberSeq
  ( fst (FibsIsoFiberFiberSeq F))
  ( snd (FibsIsoFiberFiberSeq F))
  ( alternativeIteratedPuppeFiberFiberCase
    ( FiberSeqProj F))

-- this needs tidying up!
{-altIteratedPuppeEqIteratedPuppe' : {B C : Pointed ℓ} (f : B →∙ C)
  → FiberFiberSeq (inclOfFiberFiberSeq (inclOfFiberFiberSeq f))
   ≡ -}

  altIteratedPuppeEqIteratedPuppe : {A B C : Pointed ℓ} (F : FiberSeq A B C)
    → alternativeIteratedPuppe F ≡ puppe (puppe F)
--altIteratedPuppeEqIteratedPuppe F = {!!}-}

{-
  twiceIteratedPuppeIncl : {A B C : Pointed ℓ} (F : FiberSeq A B C)
    → fst (FiberSeqIncl (puppe (puppe (puppe F))))
     ≡ λ p → sym (snd (FiberSeqIncl F))
            ∙ cong (fst (FiberSeqIncl F)) (sym p)
            ∙ snd (FiberSeqIncl F)
{-twiceIteratedPuppeIncl F =
   fst (FiberSeqIncl (puppe (puppe (puppe F))))
  ≡⟨
     cong
     ( λ G → fst (FiberSeqIncl G))
     ( sym (altIteratedPuppeEqIteratedPuppe (puppe F)))
   ⟩
   fst (FiberSeqIncl (alternativeIteratedPuppe (puppe F)))
  ≡⟨
     cong fst
     ( BaseIsoFiberSeqIncl ( fst (FibsIsoFiberFiberSeq (puppe F)))
       ( snd (FibsIsoFiberFiberSeq (puppe F)))
       ( alternativeIteratedPuppeFiberFiberCase
         ( FiberSeqProj (puppe F))))
   ⟩
   fst (FiberSeqIncl
        ( alternativeIteratedPuppeFiberFiberCase
          ( FiberSeqProj (puppe F))))
  ≡⟨
     cong fst
     ( FiberIsoFiberSeqIncl
       ( fst (puppeFiberIso (FiberSeqProj (puppe F))))
       ( snd (puppeFiberIso (FiberSeqProj (puppe F))))
       ( TotalIsoFiberSeq
         ( fst (puppeTotalIso (FiberSeqProj (puppe F))))
         ( snd (puppeTotalIso (FiberSeqProj (puppe F))))
         ( FiberFiberSeq
           ( inclOfFiberFiberSeq
             ( inclOfFiberFiberSeq
               ( FiberSeqProj (puppe F)))))))
   ⟩
   ( fst (FiberSeqIncl
          ( TotalIsoFiberSeq
            ( fst (puppeTotalIso (FiberSeqProj (puppe F))))
            ( snd (puppeTotalIso (FiberSeqProj (puppe F))))
            ( FiberFiberSeq
              ( inclOfFiberFiberSeq
                ( inclOfFiberFiberSeq
                  ( FiberSeqProj (puppe F))))))))
   ∘ (Iso.inv
      ( fst (puppeFiberIso
             ( FiberSeqProj (puppe F)))))
  ≡⟨
     (λ i →
         fst ( (TotalIsoFiberSeqIncl
                ( fst (puppeTotalIso (FiberSeqProj (puppe F))))
                ( snd (puppeTotalIso (FiberSeqProj (puppe F))))
                ( FiberFiberSeq
                  ( inclOfFiberFiberSeq
                    ( inclOfFiberFiberSeq
                      ( FiberSeqProj (puppe F)))))) i)
        ∘ (Iso.inv
           ( fst (puppeFiberIso
                  ( FiberSeqProj (puppe F))))))
   ⟩
   ( Iso.fun
     ( fst (puppeTotalIso
           ( FiberSeqProj (puppe F)))))
   ∘ (fst (FiberSeqIncl
           ( FiberFiberSeq
             ( inclOfFiberFiberSeq
               ( inclOfFiberFiberSeq
                 ( FiberSeqProj (puppe F)))))))
   ∘ (Iso.inv
      ( fst (puppeFiberIso
             ( FiberSeqProj (puppe F)))))
  ≡⟨
     refl
   ⟩
   ( Iso.fun
     ( fst (puppeTotalIso
            ( FiberSeqProj (puppe F)))))
   ∘ (fst (FiberSeqIncl
           ( FiberFiberSeq
             ( inclOfFiberFiberSeq
               ( inclOfFiberFiberSeq
                 ( FiberSeqProj (puppe F)))))))
   ∘ ( λ p →
            ( ( (pt (FiberSeqFiber F))
              , (snd (FiberSeqProj (puppe F))))
            , p)
          , refl)
  ≡⟨
     (λ i →
         ( Iso.fun
           ( fst (puppeTotalIso
                  ( FiberSeqProj (puppe F)))))
         ∘ fst ( ( InclOfFiberFiberSeq
                   ( inclOfFiberFiberSeq
                     ( inclOfFiberFiberSeq
                       ( FiberSeqProj (puppe F))))) i)
         ∘ ( λ p →
                  ( ( (pt (FiberSeqFiber F))
                    , (snd (FiberSeqProj (puppe F))))
                  , p)
                , refl))
   ⟩
     (Iso.fun
      ( fst (puppeTotalIso
             ( FiberSeqProj (puppe F)))))
   ∘ (fst (inclOfFiberFiberSeq
           ( inclOfFiberFiberSeq
             ( inclOfFiberFiberSeq
               ( FiberSeqProj (puppe F))))))
   ∘ (λ p →
         ( ( (pt (FiberSeqFiber F))
           , (snd (FiberSeqProj (puppe F))))
         , p)
       , refl)
  ≡⟨
     refl
   ⟩
     (Iso.fun (fst
               ( puppeTotalIso
                 ( FiberSeqProj (puppe F)))))
   ∘ (λ p →
         ( ( (pt (FiberSeqFiber F))
           , (snd (FiberSeqProj (puppe F))))
         , p))
  ≡⟨
     refl
   ⟩
   (λ p →
       ( sym
         ( snd (FiberSeqProj (puppe F))))
       ∙ cong
         ( fst (FiberSeqProj (puppe F)))
         ( sym p)
       ∙ snd (FiberSeqProj (puppe F)))
  ≡⟨
     (λ i →
         ( λ p →
              ( sym
                ( snd ((puppeProjEqFibIncl F) i)))
              ∙ cong
                ( fst ((puppeProjEqFibIncl F) i))
                ( sym p)
              ∙ snd ((puppeProjEqFibIncl F) i)))
   ⟩
   (λ p →
       ( sym (snd (FiberSeqIncl F)))
       ∙ cong (fst (FiberSeqIncl F)) (sym p)
       ∙ snd (FiberSeqIncl F)) ∎-}


  twiceIteratedPuppeProj : {A B C : Pointed ℓ} (F : FiberSeq A B C)
    → fst (FiberSeqProj (puppe (puppe (puppe F))))
     ≡ λ p → sym (snd (FiberSeqProj F))
            ∙ cong (fst (FiberSeqProj F)) (sym p)
            ∙ snd (FiberSeqProj F)
{-twiceIteratedPuppeProj F =
  fst (FiberSeqProj (puppe (puppe (puppe F))))
 ≡⟨
    cong fst (puppeProjEqFibIncl (puppe (puppe F)))
  ⟩
  fst (FiberSeqIncl (puppe (puppe F)))
 ≡⟨
    cong (λ G → fst (FiberSeqIncl G)) (altIteratedPuppeEqIteratedPuppe F ⁻¹)
  ⟩
  fst (FiberSeqIncl (alternativeIteratedPuppe F))
 ≡⟨
    cong fst
     ( BaseIsoFiberSeqIncl ( fst (FibsIsoFiberFiberSeq F))
     ( snd (FibsIsoFiberFiberSeq F))
     ( alternativeIteratedPuppeFiberFiberCase
       ( FiberSeqProj F)))
  ⟩
  fst (FiberSeqIncl (alternativeIteratedPuppeFiberFiberCase (FiberSeqProj F)))
 ≡⟨
   cong fst
   ( FiberIsoFiberSeqIncl
     ( fst (puppeFiberIso (FiberSeqProj F)))
     ( snd (puppeFiberIso (FiberSeqProj F)))
     ( TotalIsoFiberSeq
       ( fst (puppeTotalIso (FiberSeqProj F)))
       ( snd (puppeTotalIso (FiberSeqProj F)))
       ( FiberFiberSeq
         ( inclOfFiberFiberSeq
           ( inclOfFiberFiberSeq
             ( FiberSeqProj F))))))
  ⟩
  fst (FiberSeqIncl
       ( TotalIsoFiberSeq
         ( fst (puppeTotalIso (FiberSeqProj F)))
         ( snd (puppeTotalIso (FiberSeqProj F)))
         ( FiberFiberSeq
           ( inclOfFiberFiberSeq
             ( inclOfFiberFiberSeq
               ( FiberSeqProj F))))))
  ∘ Iso.inv (fst (puppeFiberIso (FiberSeqProj F)))
 ≡⟨
    (λ i → fst ( ( TotalIsoFiberSeqIncl
                    ( fst (puppeTotalIso (FiberSeqProj F)))
                    ( snd (puppeTotalIso (FiberSeqProj F)))
                    ( FiberFiberSeq
                      ( inclOfFiberFiberSeq
                        ( inclOfFiberFiberSeq
                          ( FiberSeqProj F))))) i)
            ∘ Iso.inv (fst (puppeFiberIso (FiberSeqProj F))))
  ⟩
  Iso.fun
  ( fst (puppeTotalIso (FiberSeqProj F)))
  ∘ fst (FiberSeqIncl
         ( FiberFiberSeq
           ( inclOfFiberFiberSeq
             ( inclOfFiberFiberSeq
               ( FiberSeqProj F)))))
  ∘ Iso.inv (fst (puppeFiberIso (FiberSeqProj F)))
 ≡⟨
    (λ i →
        Iso.fun
        ( fst (puppeTotalIso (FiberSeqProj F)))
        ∘ fst ( ( InclOfFiberFiberSeq
                  ( inclOfFiberFiberSeq
                    ( inclOfFiberFiberSeq
                      ( FiberSeqProj F)))) i)
        ∘ Iso.inv (fst (puppeFiberIso (FiberSeqProj F))))
  ⟩
  Iso.fun
  ( fst
    ( puppeTotalIso
      ( FiberSeqProj F)))
  ∘ fst
    ( inclOfFiberFiberSeq
      ( inclOfFiberFiberSeq
        ( inclOfFiberFiberSeq
          ( FiberSeqProj F))))
  ∘ Iso.inv
    ( fst
      ( puppeFiberIso
        ( FiberSeqProj F)))
 ≡⟨
    refl
  ⟩
  (λ p →
      ( sym (snd (FiberSeqProj F))
      ∙ cong (fst (FiberSeqProj F)) (sym p)
      ∙ snd (FiberSeqProj F))) ∎-}-}
