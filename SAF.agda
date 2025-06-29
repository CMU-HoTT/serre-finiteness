module SAF where

open import Everything

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.DirectProduct
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin.Inductive
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Join
open import Cubical.HITs.Truncation
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Susp
open import Cubical.Homotopy.EilenbergMacLane.Base
--open import Cubical.HITs.Sphere
open import Cubical.Algebra.AbGroup.Instances.Int renaming (ℤAbGroup to ℤ)

open import FiniteCW
open import PointedHITs
open import FPAbGroup
open import HomotopyGroups

open import FiberOrCofiberSequences.Base
open import FiberOrCofiberSequences.CofiberBase

open import Connectedness

private
  variable
    ℓ : Level

-- stably almost finite spaces

-- silly postulates
postulate
  isEquivTrnspId : {X Y : Type ℓ} (p : X ≡ Y)
    → isEquiv (transport (λ i → p i → X) (λ x → x))

  arithmetric : (M₁ M₂ k n m : ℕ)
                 → (k ≤ n + m)
                 → (M₁ + M₂ + k ≤ M₁ + n + (M₂ + m))

  arithmetric' : (M₁ M₂ k n m : ℕ)
                 → (k ≤ n + m)
                 → (M₂ + M₁ + k ≤ M₁ + n + (M₂ + m))

  isConnectedTrnspConnected : {X Y Z : Type ℓ} {n : ℕ} (p : Y ≡ Z) (f : X → Y)
    → isConnectedFun n f
    → isConnectedFun n (transport (λ i → X → (p i)) f)

-- spheres with arbitrary universe level?
postulate
  S : ℕ → Pointed ℓ


-- (n-1)-finite, perhaps?
nFinite : HLevel → Type ℓ → Type (ℓ-suc ℓ)
nFinite {ℓ} n X =
  ∥ (Σ[ C ∈ FinCW ℓ ] Σ[ f ∈ (decodeFinCW C → X) ] isConnectedFun n f) ∥₁

nFinite-isProp : {n : HLevel} {X : Type ℓ} → isProp (nFinite n X)
nFinite-isProp = squash₁

nFinite-nDim : HLevel → Type ℓ → Type (ℓ-suc ℓ)
nFinite-nDim {ℓ} n X =
  ∥ (Σ[ C ∈ Type ℓ ] Σ[ hC ∈ isNDimFinCW n C ] Σ[ f ∈ (C → X) ] isConnectedFun n f) ∥₁

nFinite-nDim' : HLevel → Type ℓ → Type (ℓ-suc ℓ)
nFinite-nDim' {ℓ} n X =
  ∥ (Σ[ C ∈ Type ℓ ] Σ[ hC ∈ isNDimFinCW n C ] Σ[ f ∈ (C → X) ] isConnectedFun (1 + n) f) ∥₁

 

nFinite-nDim-isProp : {n : HLevel} {X : Type ℓ} → isProp (nFinite-nDim n X)
nFinite-nDim-isProp = squash₁

nFinite→nDim' : {n : HLevel} {X : Type ℓ} → nFinite (1 + n) X → nFinite-nDim' n X
nFinite→nDim' {ℓ} {n} {X} hX = PT.rec squash₁ γ hX
  where

    β :(C : Σ[ C ∈ FinCW ℓ ] Σ[ f ∈ (decodeFinCW C → X) ] isConnectedFun (1 + n) f)
       → Σ[ Y ∈ Type ℓ ] (Σ[ hY ∈ (isNDimFinCW n Y) ]
                            Σ[ g ∈ (Y → typ (fst C)) ] isConnectedFun (1 + n) g)
       → nFinite-nDim' n X
    β (C , f , cf) (Y , hY , g , cg) =
      ∣ Y , hY , ((f ∘ g) , (isConnectedComp f g (1 + n) cf cg)) ∣₁
    

    γ : (Σ[ C ∈ FinCW ℓ ] Σ[ f ∈ (decodeFinCW C → X) ] isConnectedFun (1 + n) f)
        → nFinite-nDim' n X
    γ (C , f , cf) = PT.rec squash₁ (β (C , f , cf)) (mapFromNSkel (typ C) (snd C) n)

{-nFinite→nDim' : {n : HLevel} {X : Type ℓ} → nFinite n X → nFinite-nDim' n X
nFinite→nDim' {ℓ} {n} {X} hX = ?-}

-- closure of n-finiteness

cofNFinite'' : {n : ℕ} {X Y Z : Pointed ℓ} (CS : CofiberSeq X Y Z)
  → nFinite-nDim' n (typ (CofiberSeqDom CS))
  → nFinite (2 + n) (typ (CofiberSeqExt CS))
  → nFinite (2 + n) (typ (CofiberSeqCof CS))
cofNFinite'' {ℓ} {n} CS hDom hExt =
  PT.rec squash₁ step2 hDom
 where
   step0 :  (C1 : Σ[ C ∈ Type ℓ ] Σ[ hC ∈ isNDimFinCW n C ]
                                  Σ[ f ∈ (C → (typ (CofiberSeqDom CS))) ]
                                  isConnectedFun (1 + n) f)
         → (D1 : Σ[ C ∈ FinCW ℓ ]
                  Σ[ f ∈ (decodeFinCW C → (typ (CofiberSeqExt CS))) ]
                    isConnectedFun (2 + n) f)
         → (Σ[ l ∈ ((fst C1) → (typ (fst D1))) ]
             ((fst (snd D1)) ∘ l
               ≡ (fst (CofiberSeqInc CS) ∘ (fst (snd (snd C1))))))
         → nFinite (2 + n) (typ (CofiberSeqCof CS))
   step0 (C , hC , f , cf) (D , g , cg) (l , p) =
     ∣ ((typ (CofiberSeqCof₋ (cofiber-CofiberSeq₋ l))) ,
       isFinCWCofiberSeq₋
         (cofiberDom-isFinCWCofiberSeq₋ l (isNDimFinCW→isFinCW hC))
         (cofiberExt-isFinCWCofiberSeq₋ l (snd D))) ,
       (fst (CofiberSeqMap-cofiber l CS f g p)) ,
       CofiberSeqMapConn-cofiber (1 + n) l CS f g p cf cg ∣₁

   step1 : (Σ[ C ∈ Type ℓ ] Σ[ hC ∈ isNDimFinCW n C ]
                            Σ[ f ∈ (C → (typ (CofiberSeqDom CS))) ]
                            isConnectedFun (1 + n) f)
         → (Σ[ C ∈ FinCW ℓ ]
             Σ[ f ∈ (decodeFinCW C → (typ (CofiberSeqExt CS))) ]
             isConnectedFun (2 + n) f)
         → nFinite (2 + n) (typ (CofiberSeqCof CS))
   step1 (C , hC , f , cf) (D , g , cg) =
     PT.rec squash₁ (step0 (C , hC , f , cf) (D , g , cg)) (liftFromNDimFinCW n C hC g cg ((fst (CofiberSeqInc CS)) ∘ f))

   step2 : (Σ[ C ∈ Type ℓ ] Σ[ hC ∈ isNDimFinCW n C ]
                            Σ[ f ∈ (C → (typ (CofiberSeqDom CS))) ]
                            isConnectedFun (1 + n) f)
           → nFinite (2 + n) (typ (CofiberSeqCof CS))
   step2 (C , hC , f , cf) =
     PT.rec squash₁ (step1 (C , hC , f , cf)) hExt

cofNFinite' : {n : ℕ} {X Y Z : Pointed ℓ} (CS : CofiberSeq X Y Z)
  → nFinite (1 + n) (typ (CofiberSeqDom CS))
  → nFinite (2 + n) (typ (CofiberSeqExt CS))
  → nFinite (2 + n) (typ (CofiberSeqCof CS))
cofNFinite' {ℓ = ℓ} {n = n} CS hDom hExt =
  cofNFinite'' CS (nFinite→nDim' hDom) hExt

cofNFinite : {n : ℕ} {X Y Z : Pointed ℓ} → CofiberSeq X Y Z
    → nFinite (1 + n) (typ X)
    → nFinite (2 + n) (typ Y)
    → nFinite (2 + n) (typ Z)
cofNFinite {ℓ} {n} CS hX hY =
  transport (λ i → nFinite (2 + n) (typ (CofiberSeqCof-Id {S = CS} i)))
            (cofNFinite' CS
              (transport (λ i → nFinite (1 + n) (typ (CofiberSeqDom-Id {S = CS} (~ i)))) hX)
              (transport (λ i → nFinite (2 + n) (typ (CofiberSeqExt-Id {S = CS} (~ i)))) hY))

-- should change to use pointed suspension
stablyNFinite : HLevel → Pointed ℓ → Type (ℓ-suc ℓ)
stablyNFinite {ℓ} n X = ∥ (Σ[ m ∈ ℕ ] nFinite (m + n) (Susp^ m (typ X))) ∥₁

stablyNFinite' : HLevel → Pointed ℓ → Type (ℓ-suc ℓ)
stablyNFinite' {ℓ} n X =
  ∥ (Σ[ m ∈ ℕ ] (Σ[ C ∈ FinCW ℓ ]
     Σ[ f ∈ (decodeFinCW C → (Susp^ m (typ X))) ]
     isConnectedFun (m + n) f)) ∥₁

stablyNFinite-isProp : {n : HLevel} {X : Pointed ℓ} → isProp (stablyNFinite n X)
stablyNFinite-isProp = squash₁

stablyNFinite'-isProp : {n : HLevel} {X : Pointed ℓ} → isProp (stablyNFinite' n X)
stablyNFinite'-isProp = squash₁

stablyNFinite→stablyNFinite' : {n : HLevel} {X : Pointed ℓ}
  → stablyNFinite n X → stablyNFinite' n X
stablyNFinite→stablyNFinite' {X = X} hX =
  PT.rec (stablyNFinite'-isProp {X = X})
  (λ hX' → PT.rec (stablyNFinite'-isProp {X = X})
  (λ hX'' → ∣ (fst hX') , hX'' ∣₁) (snd hX')) hX

stablyNFinite'→stablyNFinite : {n : HLevel} {X : Pointed ℓ}
  → stablyNFinite' n X → stablyNFinite n X
stablyNFinite'→stablyNFinite {X = X} hX =
  PT.rec squash₁ (λ hX' → ∣ (fst hX') , ∣ snd hX' ∣₁ ∣₁) hX

saf : Pointed ℓ → Type (ℓ-suc ℓ)
saf X = (n : ℕ) → stablyNFinite n X

saf-isProp : {X : Pointed ℓ} → isProp (saf X)
saf-isProp {X = X} = isPropΠ (λ n → stablyNFinite-isProp {n = n} {X = X})

-- depends on the implementation of FinCW
isFinCW→saf : {X : Pointed ℓ} → isFinCW (typ X) → saf X
isFinCW→saf {ℓ = ℓ }{X = X} hX =
  PT.rec (saf-isProp {X = X}) (λ p n →
                    ∣ 0 , ∣ (fst p) ,
                             (transport (λ i → (snd p i) → (typ X)) (λ x → x)
                            , isEquiv→isConnected (transport (λ i → (snd p i) → (typ X))
                                      (λ x → x))
                                      (lem p) n) ∣₁ ∣₁)
                           (isFinCW-def-fun hX)
  where
  lem : (p : Σ (FinCW ℓ) (λ v → fst X ≡ decodeFinCW v))
    → isEquiv (transport (λ i → snd p i → typ X) (λ x → x))
  lem p = isEquivTrnspId (snd p)

postulate
  -- silly
  saf-Fin : ∀ n (b : Fin n) → saf (Fin n , b)

  EMDirProd : (H K : AbGroup ℓ) (n : ℕ)
    → (EM∙ (AbDirProd H K) n)
       ≡ (EM∙ H n) ×∙ (EM∙ K n)

  EM₁ℤ : (EM∙ {ℓ-zero} ℤ 1) ≡ S 1 --S¹

  saf-Sn : ∀ n → saf (S {ℓ} n)

-- all just arithmetic
stablyNFiniteOfSusp : (n : HLevel) (A : Pointed ℓ)
      → stablyNFinite (suc n) (S∙ A) → stablyNFinite n A
stablyNFiniteOfSusp n A = PT.rec (stablyNFinite-isProp {X = A})
  λ p → ∣ suc (fst p) , PT.rec nFinite-isProp (λ x → ∣ (fst x) , (fst (snd x)) ,
                        transport (λ i → isConnectedFun (+-suc (fst p) n i)
                                                         (fst (snd x)))
                                  (snd (snd x)) ∣₁) (snd p) ∣₁

-- need definitions or helper lemmas about cofiber sequences (and finite CW complexes?)
postulate
  stablyNFiniteExtension : {n : HLevel} {A B C : Pointed ℓ} (S : CofiberSeq A B C)
      → stablyNFinite n A → stablyNFinite n C → stablyNFinite n B
--stablyNFiniteExtension Co hA hC = {!!}

postulate
  safCofiber : {A B C : Pointed ℓ} → CofiberSeq A B C
    → saf A → saf B → saf C

  safExtension : {A B C : Pointed ℓ} → CofiberSeq A B C
    → saf A → saf C → saf B

-- hmm
postulate
  saf× : {A B : Pointed ℓ} → saf A → saf B → saf (A ×∙ B)

  safS¹× : {A : Pointed ℓ} → saf A → saf (S¹∙ ×∙ A)

  safS1× : {A : Pointed ℓ} → saf A → saf ((S {ℓ} 1) ×∙ A)


stablyNFiniteJoin' : {X₁ X₂ : Pointed ℓ} (m₁ n₁ m₂ n₂ : HLevel)
  (hmn₁ : m₁ ≤ n₁)
  (hXm₁ : isConnected m₁ (typ X₁)) (hXn₁ : stablyNFinite' n₁ X₁)
    (hXm₂ : isConnected m₂ (typ X₂)) (hXn₂ : stablyNFinite' n₂ X₂)
  (k : HLevel) (hk₁ : k ≤ n₁ + m₂) (hk₂ : k ≤ n₂ + m₁)
  → stablyNFinite' k (join∙ X₁ X₂)
stablyNFiniteJoin' {ℓ} {X₁} {X₂}
  m₁ n₁ m₂ n₂ (a , p) hXm₁ hXn₁ hXm₂ hXn₂ k hk₁ hk₂ =
  PT.rec (stablyNFinite'-isProp {ℓ} {k} {join∙ X₁ X₂})
     γ hXn₁
  where
    postulate
      joinSuspTrick : (M₁ M₂ : ℕ) → Susp^ (M₁ + M₂) (join (fst X₁) (fst X₂))
                                     ≡ join (Susp^ M₁ (typ X₁))
                                            (Susp^ M₂ (typ X₂))

      arithmetic : (M₁ : ℕ) → (a + (M₁ + m₁)) ≡ (M₁ + n₁)

    connectivityC₁ : (M₁ : ℕ) (C₁ : Type ℓ)
                     (f : C₁ → (Susp^ M₁ (typ X₁)))
                     (cf : isConnectedFun (M₁ + n₁) f)
                  → isConnected (M₁ + m₁) C₁
    connectivityC₁ M₁ C₁ f cf = 
                  isConnectedFun→isConnected (M₁ + m₁)
                    (isConnectedComp (λ _ → tt) f (M₁ + m₁)
                      (isConnected→isConnectedFun (M₁ + m₁)
                        (Susp^-conn m₁ M₁ (typ X₁) hXm₁))
                      (isConnectedFunSubtr (M₁ + m₁) a f
                      (transport (λ i → isConnectedFun (arithmetic M₁ (~ i)) f)
                                 cf)))


    β : (Σ[ m ∈ ℕ ] (Σ[ C ∈ FinCW ℓ ]
     Σ[ f ∈ (decodeFinCW C → (Susp^ m (typ X₁))) ]
     isConnectedFun (m + n₁) f))
      → (Σ[ m ∈ ℕ ] (Σ[ C ∈ FinCW ℓ ]
     Σ[ f ∈ (decodeFinCW C → (Susp^ m (typ X₂))) ]
     isConnectedFun (m + n₂) f))
      → stablyNFinite' k (join∙ X₁ X₂)
    β (M₁ , C₁ , f₁ , cf₁) (M₂ , C₂ , f₂ , cf₂) =
      ∣ M₁ + M₂ , ((join (typ C₁) (typ C₂)) , isFinCWJoin (snd C₁) (snd C₂))
               , transport (λ i → join (typ C₁) (typ C₂)
                                → joinSuspTrick M₁ M₂ (~ i)) (join→ f₁ f₂)
               , isConnectedTrnspConnected (sym (joinSuspTrick M₁ M₂))
                                           (join→ f₁ f₂)
                   (isConnectedFunJoin f₁ f₂ (M₁ + n₁) (M₂ + n₂) (M₁ + m₁)
                                       (M₂ + m₂) (M₁ + M₂ + k)
                                       (arithmetric M₁ M₂ k n₁ m₂ hk₁)
                                       (arithmetric' M₂ M₁ k n₂ m₁ hk₂)
                                       cf₁ cf₂ (connectivityC₁ M₁ (typ C₁) f₁ cf₁)
                                       (Susp^-conn m₂ M₂ (typ X₂) hXm₂)) ∣₁


    γ : (Σ[ m ∈ ℕ ] (Σ[ C ∈ FinCW ℓ ]
     Σ[ f ∈ (decodeFinCW C → (Susp^ m (typ X₁))) ]
     isConnectedFun (m + n₁) f))
        → stablyNFinite' k (join∙ X₁ X₂)
    γ hX₁ = PT.rec (stablyNFinite'-isProp {ℓ} {k} {join∙ X₁ X₂})
                   (β hX₁)
                   hXn₂

stablyNFiniteJoin : {X₁ X₂ : Pointed ℓ} (m₁ n₁ m₂ n₂ : HLevel)
  (hmn₁ : m₁ ≤ n₁)
  (hXm₁ : isConnected m₁ (typ X₁)) (hXn₁ : stablyNFinite n₁ X₁)
    (hXm₂ : isConnected m₂ (typ X₂)) (hXn₂ : stablyNFinite n₂ X₂)
  (k : HLevel) (hk₁ : k ≤ n₁ + m₂) (hk₂ : k ≤ n₂ + m₁)
  → stablyNFinite k (join∙ X₁ X₂)
stablyNFiniteJoin {ℓ} {X₁} {X₂} m₁ n₁ m₂ n₂ hmn₁ hXm₁ hXn₁ hXm₂ hXn₂ k hk₁ hk₂ =
  stablyNFinite'→stablyNFinite {X = join∙ X₁ X₂}
  (stablyNFiniteJoin' {ℓ} {X₁} {X₂} m₁ n₁ m₂ n₂ hmn₁ hXm₁
  (stablyNFinite→stablyNFinite' {X = X₁} hXn₁) hXm₂
  (stablyNFinite→stablyNFinite' {X = X₂} hXn₂) k hk₁ hk₂)

postulate
  stablyNFiniteApprox : {X Y : Pointed ℓ} (f : X →∙ Y)
    (n : HLevel) (hf : isConnectedFun n (fst f))
    → stablyNFinite (1 + n) X → stablyNFinite n Y

  stablyNFiniteApprox' : {X Y : Pointed ℓ} (f : X →∙ Y)
    (n : HLevel) (hf : isConnectedFun n (fst f))
    → stablyNFinite n Y → stablyNFinite n X
