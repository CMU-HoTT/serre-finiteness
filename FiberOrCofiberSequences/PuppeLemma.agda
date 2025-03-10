{-# OPTIONS --lossy-unification #-}
module FiberOrCofiberSequences.PuppeLemma where

open import Everything

open import Cubical.Data.Sigma
open import Cubical.Homotopy.Loopspace

open import PointedHITs

open import FiberOrCofiberSequences.Base
open import FiberOrCofiberSequences.CofiberBase

private
  variable
    ℓ : Level

puppeTotalIso2 : (B C : Pointed ℓ) (f : B →∙ C) →
  Iso (typ (fiber∙ (inclOfFiberFiberSeq f)))
      (Σ[ b ∈ (typ B) ] ((fst f) b ≡ pt C) × (b ≡ pt B))
Iso.fun (puppeTotalIso2 B C f) ((b , p) , q) = b , (p , q)
Iso.inv (puppeTotalIso2 B C f) (b , (p , q)) = (b , p) , q
Iso.rightInv (puppeTotalIso2 B C f) tr = refl
Iso.leftInv (puppeTotalIso2 B C f) tr = refl

-- needs tidying up
-- try making this a ≡⟨ ⟩ type thing! 
puppeTotalIso1 : (B C : Pointed ℓ) (f : B →∙ C) →
  Iso (Σ[ b ∈ (typ B) ] ((fst f) b ≡ pt C) × (b ≡ pt B)) (typ (Ω C))
Iso.fun (puppeTotalIso1 B C f) (b , (p , q)) =
  sym (snd f) ∙ cong (fst f) (sym q) ∙ p
Iso.inv (puppeTotalIso1 B C f) p = (pt B) , (((snd f) ∙ p) , refl)
Iso.rightInv (puppeTotalIso1 B C f) p =
  cong
  ( sym (snd f) ∙_)
  ( lUnit _ ⁻¹)
  ∙ assoc
    ( sym (snd f))
    ( snd f)
    ( p)
  ∙ cong
    ( _∙ p)
    ( lCancel _)
  ∙ lUnit _ ⁻¹
Iso.leftInv (puppeTotalIso1 B C f) (b , (p , q)) =
  ΣPathP
  ( (sym q)
  , ( toPathP
      ( ≡-×
        ( transportFunPathLemma'
          ( fst f)
          ( q)
          ( snd f
          ∙ sym (snd f)
          ∙ cong (fst f) (sym q)
          ∙ p)
        ∙ cong
          ( cong (fst f) q ∙_)
          ( assoc
            ( snd f)
            ( sym (snd f))
            ( cong (fst f) (sym q)
            ∙ p)
          ∙ cong
            ( _∙ (cong (fst f) (sym q) ∙ p))
            ( rCancel _))
        ∙ cong
          ( cong (fst f) q ∙_)
          ( lUnit _ ⁻¹)
        ∙ assoc
          ( cong (fst f) q)
          ( cong (fst f) (sym q))
          ( p)
        ∙ cong
          ( _∙ p)
          ( rCancel _)
        ∙ lUnit _ ⁻¹)
        ( transportFunPathLemma'' b (pt B) q))))

puppeTotalIso : {B C : Pointed ℓ} (f : B →∙ C) →
  Σ[ H ∈ Iso (typ (fiber∙ (inclOfFiberFiberSeq f))) (typ (Ω C)) ]
  Iso.fun H  (pt (fiber∙ (inclOfFiberFiberSeq f))) ≡ (pt (Ω C))
fst (puppeTotalIso f) = compIso (puppeTotalIso2 _ _ f) (puppeTotalIso1 _ _ f)
snd (puppeTotalIso f) = cong (sym (snd f) ∙_) (lUnit _ ⁻¹) ∙ lCancel _

puppeFiberIso2 : (B C : Pointed ℓ) (f : B →∙ C) →
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
fst (puppeFiberIso f) = compIso (puppeFiberIso2 _ _ f) (puppeFiberIso1 _ _ f)
snd (puppeFiberIso f) = lUnit _ ⁻¹

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
puppeProjEqFibIncl : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  → FiberSeqProj (puppe F) ≡ FiberSeqIncl F
puppeProjEqFibIncl F =
  ( TotalIsoFiberSeqProj
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
           ( FiberSeqProj F))))

alternativeIteratedPuppeFiberFiberCase : {B C : Pointed ℓ} (f : B →∙ C)
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
altIteratedPuppeEqIteratedPuppe : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  → alternativeIteratedPuppe F ≡ puppe (puppe F)
altIteratedPuppeEqIteratedPuppe F =
   EqOfEqFiberSeqProj
   ( alternativeIteratedPuppe F)
   ( puppe (puppe F))
   ( FiberSeqProj (alternativeIteratedPuppe F)
 ≡⟨
    (BaseIsoFiberSeqProj
     ( fst (FibsIsoFiberFiberSeq F))
     ( snd (FibsIsoFiberFiberSeq F))
     ( alternativeIteratedPuppeFiberFiberCase (FiberSeqProj F)))
  ⟩
  ( (Iso.fun (fst (FibsIsoFiberFiberSeq F))
  , snd (FibsIsoFiberFiberSeq F))
  ∘∙ ( FiberSeqProj
       ( alternativeIteratedPuppeFiberFiberCase (FiberSeqProj F))))
 ≡⟨
    cong
    ( (Iso.fun (fst (FibsIsoFiberFiberSeq F))
    , snd (FibsIsoFiberFiberSeq F)) ∘∙_)
    ( FiberIsoFiberSeqProj _ _ _)
  ⟩
  ( (Iso.fun (fst (FibsIsoFiberFiberSeq F))
  , snd (FibsIsoFiberFiberSeq F))
  ∘∙ ( FiberSeqProj
       ( TotalIsoFiberSeq _ _ _)))
 ≡⟨
    cong
    ( (Iso.fun (fst (FibsIsoFiberFiberSeq F))
    , snd (FibsIsoFiberFiberSeq F)) ∘∙_)
    ( TotalIsoFiberSeqProj _ _ _)
  ⟩
  ( (Iso.fun (fst (FibsIsoFiberFiberSeq F))
  , snd (FibsIsoFiberFiberSeq F))
  ∘∙ ( FiberSeqProj
       ( FiberFiberSeq
         ( inclOfFiberFiberSeq
           ( inclOfFiberFiberSeq
             ( FiberSeqProj F))))
  ∘∙ ( Iso.inv (fst (puppeTotalIso (FiberSeqProj F)))
     , cong
       ( Iso.inv (fst (puppeTotalIso (FiberSeqProj F))))
       ( sym (snd (puppeTotalIso (FiberSeqProj F))))
       ∙ Iso.leftInv (fst (puppeTotalIso (FiberSeqProj F))) _)))
 ≡⟨
    ( λ i →
         ( Iso.fun (fst (FibsIsoFiberFiberSeq F))
         , snd (FibsIsoFiberFiberSeq F))
         ∘∙ ( ( ( ProjOfFiberFiberSeq
                  ( inclOfFiberFiberSeq
                    ( inclOfFiberFiberSeq
                      ( FiberSeqProj F)))
                ∙ sym (InclOfFiberFiberSeq
                       ( inclOfFiberFiberSeq
                         ( FiberSeqProj F)))) i)
         ∘∙ ( Iso.inv (fst (puppeTotalIso (FiberSeqProj F)))
            , cong
              ( Iso.inv (fst (puppeTotalIso (FiberSeqProj F))))
              ( sym (snd (puppeTotalIso (FiberSeqProj F))))
              ∙ Iso.leftInv
                ( fst (puppeTotalIso (FiberSeqProj F)))
                ( ( (pt (FiberSeqTotal F))
                  , (snd (FiberSeqProj F)))
                , refl))))
     ⟩
  ( (Iso.fun (fst (FibsIsoFiberFiberSeq F))
  , snd (FibsIsoFiberFiberSeq F))
  ∘∙ ( FiberSeqIncl
       ( FiberFiberSeq
         ( inclOfFiberFiberSeq (FiberSeqProj F)))
  ∘∙ ( Iso.inv (fst (puppeTotalIso (FiberSeqProj F)))
     , cong
       ( Iso.inv (fst (puppeTotalIso (FiberSeqProj F))))
       ( sym (snd (puppeTotalIso (FiberSeqProj F))))
       ∙ Iso.leftInv (fst (puppeTotalIso (FiberSeqProj F))) _)))
 ≡⟨
    cong
    ( (Iso.fun (fst (FibsIsoFiberFiberSeq F))
    , snd (FibsIsoFiberFiberSeq F)) ∘∙_)
    ( sym (FiberIsoFiberSeqIncl
           ( fst (puppeTotalIso (FiberSeqProj F)))
           ( snd (puppeTotalIso (FiberSeqProj F)))
           ( FiberFiberSeq
             ( inclOfFiberFiberSeq (FiberSeqProj F)))))
  ⟩
   ( (Iso.fun (fst (FibsIsoFiberFiberSeq F))
   , snd (FibsIsoFiberFiberSeq F))
   ∘∙ FiberSeqIncl
      ( puppeFiberFiberCase
        ( FiberSeqProj F)))
 ≡⟨
    sym
    ( TotalIsoFiberSeqIncl
      ( fst (FibsIsoFiberFiberSeq F))
      ( snd (FibsIsoFiberFiberSeq F))
      ( puppeFiberFiberCase (FiberSeqProj F)))
  ⟩
   FiberSeqIncl (puppe F)
 ≡⟨
    sym (puppeProjEqFibIncl (puppe F))
  ⟩
   FiberSeqProj (puppe (puppe F)) ∎)

twiceIteratedPuppeIncl : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  → fst (FiberSeqIncl (puppe (puppe (puppe F))))
   ≡ λ p → sym (snd (FiberSeqIncl F))
            ∙ cong (fst (FiberSeqIncl F)) (sym p)
            ∙ snd (FiberSeqIncl F)
twiceIteratedPuppeIncl F =
   fst (FiberSeqIncl (puppe (puppe (puppe F))))
  ≡⟨
     cong
     ( λ G → fst (FiberSeqIncl G))
     ( sym (altIteratedPuppeEqIteratedPuppe (puppe F)))
   ⟩
   fst (FiberSeqIncl (alternativeIteratedPuppe (puppe F)))
  ≡⟨
     cong fst
     ( BaseIsoFiberSeqIncl _
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
       ∙ snd (FiberSeqIncl F)) ∎

twiceIteratedPuppeProj : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  → fst (FiberSeqProj (puppe (puppe (puppe F))))
   ≡ λ p → sym (snd (FiberSeqProj F))
            ∙ cong (fst (FiberSeqProj F)) (sym p)
            ∙ snd (FiberSeqProj F)
twiceIteratedPuppeProj F =
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
    cong fst (BaseIsoFiberSeqIncl _ _ _)
  ⟩
  fst (FiberSeqIncl (alternativeIteratedPuppeFiberFiberCase (FiberSeqProj F)))
 ≡⟨
    cong fst (FiberIsoFiberSeqIncl _ _ _)
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
      ∙ snd (FiberSeqProj F))) ∎
