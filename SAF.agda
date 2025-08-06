module SAF where

open import Everything

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.DirectProduct
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin.Inductive
open import Cubical.Data.Sigma
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Join
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Susp
open import Cubical.HITs.Sn hiding (S)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.CW.Base
--open import Cubical.HITs.Sphere
open import Cubical.Algebra.AbGroup.Instances.Int renaming (ℤAbGroup to ℤ)
open import Cubical.CW.Instances.Lift
open import Cubical.CW.Instances.Sn

open import FiniteCW
open import PointedHITs
open import FPAbGroup
open import HomotopyGroups

open import FiberOrCofiberSequences.Base
open import FiberOrCofiberSequences.CofiberBase

open import Connectedness

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.HITs.S1
open import Cubical.HITs.EilenbergMacLane1 as EM1
open import Cubical.HITs.Sn hiding (S)

open import LastMinuteLemmas.EM

private
  variable
    ℓ : Level

-- stably almost finite spaces

-- probably this is defined elsewhere
Susp→^ : {X Y : Type ℓ} (n : ℕ) (f : X → Y) → Susp^ n X → Susp^ n Y
Susp→^ zero f = f
Susp→^ (suc n) f = Susp→^ n (suspFun f)

Susp→^-conn : {X Y : Type ℓ} (n m : ℕ) (f : X → Y) → isConnectedFun m f
            → isConnectedFun (n + m) (Susp→^ n f)
Susp→^-conn zero m f con = con
Susp→^-conn (suc n) m f con =
  subst (λ k → isConnectedFun k (Susp→^ n (suspFun f)))
        (+-suc n m)
        (Susp→^-conn n (suc m) (suspFun f)
          (isConnectedSuspFun f m con))

isConnectedPoint* : ∀ (n : HLevel) {A : Type ℓ}
  → isConnected (suc n) A
  → (a : A) → isConnectedFun n (λ(_ : Unit* {ℓ}) → a)
isConnectedPoint* n connA a₀ a =
  isConnectedRetract n
    snd (_ ,_) (λ _ → refl)
    (isConnectedPath n connA a₀ a)

isEquivTrnspId : {X Y : Type ℓ} (p : X ≡ Y)
  → isEquiv (transport (λ i → p i → X) (λ x → x))
isEquivTrnspId {X = X} p =
  transport (λ j → isEquiv (transp (λ i → p (i ∧ j) → X)
                                    (~ j) (λ x → x)))
    (idIsEquiv X)

isConnectedUnit* : (n : ℕ) → isConnected n (Unit* {ℓ})
isConnectedUnit* zero = tt* , (λ _ → refl)
isConnectedUnit* (suc n) .fst = ∣ tt* ∣
isConnectedUnit* (suc n) .snd =
  TR.elim (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _)
          λ _ → refl

arithmetric : (M₁ M₂ k n m : ℕ)
               → (k ≤ n + m)
               → (M₁ + M₂ + k ≤ M₁ + n + (M₂ + m))
arithmetric M₁ M₂ k n m p =
  subst2 (_≤_)
    (+-comm k (M₁ + M₂))
    (+-comm (n + m) (M₁ + M₂)
    ∙ sym (+-assoc M₁ M₂ (n + m))
    ∙ cong (M₁ +_) (+-assoc M₂ n m
                   ∙ cong (_+ m) (+-comm M₂ n)
                   ∙ sym (+-assoc n M₂ m))
    ∙ +-assoc M₁ n (M₂ + m))
    (≤-+k {k = M₁ + M₂} p)

arithmetric' : (M₁ M₂ k n m : ℕ)
               → (k ≤ n + m)
               → (M₂ + M₁ + k ≤ M₁ + n + (M₂ + m))
arithmetric' M₁ M₂ k n m p =
  subst2 (_≤_)
    (+-comm k (M₂ + M₁))
    (sym (+-assoc n m (M₂ + M₁))
    ∙ cong (n +_) (+-comm m (M₂ + M₁)
                ∙ (sym (+-assoc M₂ M₁ m)
                ∙ cong (M₂ +_) (+-comm M₁ m)
                ∙ +-assoc M₂ m M₁)
                ∙ +-comm (M₂ + m) M₁)
    ∙ +-assoc n M₁ (M₂ + m)
    ∙ sym (cong (_+ (M₂ + m)) (+-comm M₁ n)))
    (≤-+k {k = M₂ + M₁} p)

isConnectedTrnspConnected : {X Y Z : Type ℓ} {n : ℕ} (p : Y ≡ Z) (f : X → Y)
  → isConnectedFun n f
  → isConnectedFun n (transport (λ i → X → (p i)) f)
isConnectedTrnspConnected {X = X} {n = n} p f conf  =
  transport (λ i → isConnectedFun n
                    (transp (λ j → X → (p (j ∧ i))) (~ i) f))
    conf

-- spheres with arbitrary universe level?
S : ℕ → Pointed ℓ
S {ℓ = ℓ} n = S₊∙ n ×∙ (Unit* {ℓ} , tt*)

isFinCWS : (n : ℕ) → isFinCW (S {ℓ} n .fst)
isFinCWS n = subst isFinCW (isoToPath lem)
             (snd (finCWLift _ (_ , isFinCWSn)))
  where
  lem : Iso (Lift (S₊ n)) (S n .fst)
  lem = compIso (invIso LiftIso) (invIso rUnit*×Iso)

-- `nFinite n X` corresponds to "X is (n-1)-finite" on paper,
-- because `isConnectedFun n f` corresponds to "f is (n-2)-connected".
nFinite : HLevel → Type ℓ → Type (ℓ-suc ℓ)
nFinite {ℓ} n X =
  ∥ (Σ[ C ∈ FinCW ℓ ] Σ[ f ∈ (decodeFinCW C → X) ] isConnectedFun n f) ∥₁

nFinite-isProp : {n : HLevel} {X : Type ℓ} → isProp (nFinite n X)
nFinite-isProp = squash₁

-- "X admits an (n-2)-connected map from an (n-1)-dimensional CW complex"
nFinite-nDim : HLevel → Type ℓ → Type (ℓ-suc ℓ)
nFinite-nDim {ℓ} n X =
  ∥ (Σ[ C ∈ Type ℓ ] Σ[ hC ∈ isNDimFinCW n C ] Σ[ f ∈ (C → X) ] isConnectedFun n f) ∥₁

nFinite-nDim-isProp : {n : HLevel} {X : Type ℓ} → isProp (nFinite-nDim n X)
nFinite-nDim-isProp = squash₁

nDim→nFinite : {n : HLevel} {X : Type ℓ} → nFinite-nDim n X → nFinite n X
nDim→nFinite {ℓ} {n} {X} hX =
  PT.rec nFinite-isProp
  (λ hX' → ∣ (fst hX' , isNDimFinCW→isFinCW (fst (snd hX')))
                      , (snd (snd hX')) ∣₁)
  hX

nFinite→nDim : {n : HLevel} {X : Type ℓ} → nFinite n X → nFinite-nDim n X
nFinite→nDim {ℓ} {n} {X} hX = PT.rec squash₁ γ hX
  where

    β :(C : Σ[ C ∈ FinCW ℓ ] Σ[ f ∈ (decodeFinCW C → X) ] isConnectedFun n f)
       → Σ[ Y ∈ Type ℓ ] (Σ[ hY ∈ (isNDimFinCW n Y) ]
                            Σ[ g ∈ (Y → typ (fst C)) ] isConnectedFun n g)
       → nFinite-nDim n X
    β (C , f , cf) (Y , hY , g , cg) =
      ∣ Y , hY , ((f ∘ g) , (isConnectedComp f g n cf cg)) ∣₁


    γ : (Σ[ C ∈ FinCW ℓ ] Σ[ f ∈ (decodeFinCW C → X) ] isConnectedFun n f)
        → nFinite-nDim n X
    γ (C , f , cf) = PT.rec squash₁ (β (C , f , cf)) (mapFromNSkel (typ C) (snd C) n)

-- closure of n-finiteness under cofibers

cofNFinite'' : {n : ℕ} {X Y Z : Pointed ℓ} (CS : CofiberSeq X Y Z)
  → nFinite-nDim n (typ (CofiberSeqDom CS))
  → nFinite (1 + n) (typ (CofiberSeqExt CS))
  → nFinite (1 + n) (typ (CofiberSeqCof CS))
cofNFinite'' {ℓ} {n} CS hDom hExt =
  PT.rec squash₁ step2 hDom
 where
   step0 :  (C1 : Σ[ C ∈ Type ℓ ] Σ[ hC ∈ isNDimFinCW n C ]
                                  Σ[ f ∈ (C → (typ (CofiberSeqDom CS))) ]
                                  isConnectedFun n f)
         → (D1 : Σ[ C ∈ FinCW ℓ ]
                  Σ[ f ∈ (decodeFinCW C → (typ (CofiberSeqExt CS))) ]
                    isConnectedFun (1 + n) f)
         → (Σ[ l ∈ ((fst C1) → (typ (fst D1))) ]
             ((fst (snd D1)) ∘ l
               ≡ (fst (CofiberSeqInc CS) ∘ (fst (snd (snd C1))))))
         → nFinite (1 + n) (typ (CofiberSeqCof CS))
   step0 (C , hC , f , cf) (D , g , cg) (l , p) =
     ∣ ((typ (CofiberSeqCof₋ (cofiber-CofiberSeq₋ l))) ,
       isFinCWCofiberSeq₋
         (cofiberDom-isFinCWCofiberSeq₋ l (isNDimFinCW→isFinCW hC))
         (cofiberExt-isFinCWCofiberSeq₋ l (snd D))) ,
       (fst (CofiberSeqMap-cofiber l CS f g p)) ,
       CofiberSeqMapConn-cofiber n l CS f g p cf cg ∣₁

   step1 : (Σ[ C ∈ Type ℓ ] Σ[ hC ∈ isNDimFinCW n C ]
                            Σ[ f ∈ (C → (typ (CofiberSeqDom CS))) ]
                            isConnectedFun n f)
         → (Σ[ C ∈ FinCW ℓ ]
             Σ[ f ∈ (decodeFinCW C → (typ (CofiberSeqExt CS))) ]
             isConnectedFun (1 + n) f)
         → nFinite (1 + n) (typ (CofiberSeqCof CS))
   step1 (C , hC , f , cf) (D , g , cg) =
     PT.rec squash₁ (step0 (C , hC , f , cf) (D , g , cg))
       (liftFromNDimFinCW n C hC g (isConnectedFunSubtr n 1 g cg) ((fst (CofiberSeqInc CS)) ∘ f))

   step2 : (Σ[ C ∈ Type ℓ ] Σ[ hC ∈ isNDimFinCW n C ]
                            Σ[ f ∈ (C → (typ (CofiberSeqDom CS))) ]
                            isConnectedFun n f)
           → nFinite (1 + n) (typ (CofiberSeqCof CS))
   step2 (C , hC , f , cf) =
     PT.rec squash₁ (step1 (C , hC , f , cf)) hExt

cofNFinite' : {n : ℕ} {X Y Z : Pointed ℓ} (CS : CofiberSeq X Y Z)
  → nFinite n (typ (CofiberSeqDom CS))
  → nFinite (1 + n) (typ (CofiberSeqExt CS))
  → nFinite (1 + n) (typ (CofiberSeqCof CS))
cofNFinite' {ℓ = ℓ} {n = n} CS hDom hExt =
  cofNFinite'' CS (nFinite→nDim hDom) hExt

cofNFinite : {n : ℕ} {X Y Z : Pointed ℓ} → CofiberSeq X Y Z
    → nFinite n (typ X)
    → nFinite (1 + n) (typ Y)
    → nFinite (1 + n) (typ Z)
cofNFinite {ℓ} {n} CS hX hY =
  transport (λ i → nFinite (1 + n) (typ (CofiberSeqCof-Id {S = CS} i)))
            (cofNFinite' CS
              (transport (λ i → nFinite n (typ (CofiberSeqDom-Id {S = CS} (~ i)))) hX)
              (transport (λ i → nFinite (1 + n) (typ (CofiberSeqExt-Id {S = CS} (~ i)))) hY))

susp-nFinite : {X : Type ℓ} (n : ℕ) → nFinite n X → nFinite (suc n) (Susp X)
susp-nFinite {X = X} n = PT.map
  λ {(X , w , q)
  → (Susp (fst X)
  , isFinCWSusp {n = 1} (fst X) (snd X))
  , (suspFun w , isConnectedSuspFun w n q)}

-- If X is (n-1)-finite and f : X -> Y is (n-2)-connected then Y is (n-1)-finite.
nFiniteApprox :  {X Y : Type ℓ} (f : X → Y)
    (n : HLevel) (hf : isConnectedFun n f)
    → nFinite n X → nFinite n Y
nFiniteApprox f n hf = PT.rec squash₁ (λ hX → ∣ (fst hX) , ((f ∘ fst (snd hX)) , (isConnectedComp f (fst (snd hX)) n hf (snd (snd hX)))) ∣₁)

-- If Y is (n-1)-finite and f : X -> Y is (n-1)-connected then Y is (n-1)-finite.
nFiniteApprox' :  {X Y : Type ℓ} (f : X → Y)
  (n : HLevel) (hf : isConnectedFun (1 + n) f)
  → nFinite n Y → nFinite n X
nFiniteApprox' {ℓ} {X} {Y} f n hf hY = PT.rec nFinite-isProp γ (nFinite→nDim hY)
  where
    α : (hY : Σ[ C ∈ Type ℓ ] Σ[ hC ∈ isNDimFinCW n C ]
          Σ[ g ∈ (C → Y) ] isConnectedFun n g)
       → ∃[ l ∈ ((fst hY) → X) ] (f ∘ l ≡ (fst (snd (snd hY))))
    α (C , hC , g , cg) =
      liftFromNDimFinCW n C hC f (isConnectedFunSubtr n 1 f hf) g

    β :  (hY : Σ[ C ∈ Type ℓ ] Σ[ hC ∈ isNDimFinCW n C ]
          Σ[ g ∈ (C → Y) ] isConnectedFun n g)
         → (hl : Σ[ l ∈ ((fst hY) → X) ] (f ∘ l ≡ (fst (snd (snd hY)))))
         → (isConnectedFun n (fst hl))
    β (C , hC , g , cg) (l , hl) =
      isConnectedFunCancel' l f n hf
        (transport (λ i → isConnectedFun n (hl (~ i)))
                   cg)

    γ : (Σ[ C ∈ Type ℓ ] Σ[ hC ∈ isNDimFinCW n C ]
          Σ[ g ∈ (C → Y) ] isConnectedFun n g)
        → nFinite n X
    γ (C , hC , g , cg) =
      nDim→nFinite
        (PT.rec
           squash₁
           (λ hl → ∣ C , (hC , ((fst hl) , (β (C , hC , g , cg) hl))) ∣₁)
           (α (C , hC , g , cg)))

nFiniteDrop : {X : Type ℓ} (n : HLevel)
  → nFinite (1 + n) X → nFinite n X
nFiniteDrop n = PT.rec nFinite-isProp
                       (λ hX → ∣ (fst hX)
                                , ((fst (snd hX))
                                , isConnectedFunSubtr n 1 (fst (snd hX)) (snd (snd hX))) ∣₁)


-- should change to use pointed suspension
-- `stablyNFinite n X` means "X is stably (n-1)-finite".
stablyNFinite : HLevel → Pointed ℓ → Type (ℓ-suc ℓ)
stablyNFinite {ℓ} n X = ∥ (Σ[ m ∈ ℕ ] nFinite (m + n) (Susp^ m (typ X))) ∥₁

pointIrrelSNFnt : (n : ℕ) (X : Pointed ℓ) (x : typ X)
                  → stablyNFinite n X → stablyNFinite n (typ X , x)
pointIrrelSNFnt n X x hyp = hyp

-- alternative version of `stablyNFinite` with a single existential
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

-- `saf X` means "X is stably almost finite".
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

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.CW.Instances.Empty
open import Cubical.CW.Instances.Lift
open import Cubical.CW.Instances.Sn
open import Cubical.CW.Instances.Sigma
open import Cubical.HITs.Pushout

PushoutEmptyDomainIso* : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'}
  → Iso (Pushout {A = ⊥* {ℓ''}} {B = A} {C = B}
                  (λ()) (λ()))
         (A ⊎ B)
PushoutEmptyDomainIso* .Iso.fun (inl x) = inl x
PushoutEmptyDomainIso* .Iso.fun (inr x) = inr x
PushoutEmptyDomainIso* .Iso.inv (inl x) = inl x
PushoutEmptyDomainIso* .Iso.inv (inr x) = inr x
PushoutEmptyDomainIso* .Iso.rightInv (inl x) = refl
PushoutEmptyDomainIso* .Iso.rightInv (inr x) = refl
PushoutEmptyDomainIso* .Iso.leftInv (inl x) = refl
PushoutEmptyDomainIso* .Iso.leftInv (inr x) = refl

isFinCW⊎ : ∀ {ℓ} {A B : Type ℓ} → isFinCW A → isFinCW B
  → isFinCW (A ⊎ B) 
isFinCW⊎ {A = A} {B = B} fA fB =
  subst isFinCW
    (isoToPath PushoutEmptyDomainIso*)
    (isFinCWPushout {X = ⊥*} {A} {B}
      (λ()) (λ()) (snd (finCW⊥* _)) fA fB)

open import Cubical.Data.Unit
isFinCWFin : (n : ℕ) → isFinCW (Fin n)
isFinCWFin zero =
  subst isFinCW (ua (uninhabEquiv (λ()) ¬Fin0))
        (snd finCW⊥)
isFinCWFin (suc n) =
  subst isFinCW (isoToPath (Iso-Fin1⊎Fin-FinSuc {n}))
    (isFinCW⊎
      (subst isFinCW
        (ua (isContr→Equiv isContrUnit*
             (fzero , isPropFin1 fzero)))
        isFinCWUnit)
    (isFinCWFin n))


saf-Fin : ∀ n (b : Fin n) → saf (Fin n , b)
saf-Fin n b = isFinCW→saf {X = _ , b} (isFinCWFin n)

saf-Unit : saf {ℓ} (Unit* , tt*)
saf-Unit = isFinCW→saf {X = _ , tt*} isFinCWUnit

saf-Sn : ∀ n → saf (S {ℓ} n)
saf-Sn n = isFinCW→saf {X = _ , (ptSn n) , tt*} (isFinCWS n)

EM₁ℤ : (EM∙ {ℓ-zero} ℤ 1) ≡ S 1
EM₁ℤ = sym (ua∙ (isoToEquiv (compIso rUnit*×Iso S¹≅EM)) refl)
  where
  open import Cubical.Data.Int renaming (ℤ to Int ; _+_ to _+ℤ_)
  S¹→EM : S¹ → EM ℤ 1
  S¹→EM base = embase
  S¹→EM (loop i) = emloop 1 i

  S¹→EM-intLoop : (g : _) → cong S¹→EM (intLoop g) ≡ emloop g
  S¹→EM-intLoop (pos zero) = sym (emloop-1g _)
  S¹→EM-intLoop (pos (suc n)) =
    cong-∙ S¹→EM (intLoop (pos n)) loop
    ∙ cong₂ _∙_ (S¹→EM-intLoop (pos n)) refl
    ∙ sym (emloop-comp _ (pos n) (pos 1))
  S¹→EM-intLoop (negsuc zero) = sym (emloop-sym _ _)
  S¹→EM-intLoop (negsuc (suc n)) =
      cong-∙ S¹→EM (intLoop (negsuc n)) (sym loop)
    ∙ cong₂ _∙_ (S¹→EM-intLoop (negsuc n)) (sym (emloop-sym _ _))
    ∙ sym (emloop-comp _ (negsuc n) -1)

  EM→S¹ : EM ℤ 1 → S¹
  EM→S¹ = EM1.rec _ isGroupoidS¹ base intLoop λ g h
    → compPathL→PathP (sym (lUnit _) ∙ (intLoop-hom g h))

  S¹≅EM : Iso S¹ (EM {ℓ-zero} ℤ 1)
  S¹≅EM .Iso.fun = S¹→EM
  S¹≅EM .Iso.inv = EM→S¹
  S¹≅EM .Iso.rightInv = EM1.elimSet _ (λ _ → emsquash _ _) refl
    λ g i j → S¹→EM-intLoop g j i
  S¹≅EM .Iso.leftInv base = refl
  S¹≅EM .Iso.leftInv (loop i) j = lUnit loop (~ j) i

EMDirProd : {ℓ : Level} (H K : AbGroup ℓ) (n : ℕ)
  → EM∙ (AbDirProd H K) n ≡ (EM∙ H n) ×∙ (EM∙ K n)
EMDirProd H K n =
  ua∙ (EMDirProdEquiv H K n)
      (EMProd→ProdEM∙ H K n .snd)

-- all just arithmetic
stablyNFiniteOfSusp : (n : HLevel) (A : Pointed ℓ)
      → stablyNFinite (suc n) (S∙ A) → stablyNFinite n A
stablyNFiniteOfSusp n A = PT.rec (stablyNFinite-isProp {X = A})
  λ p → ∣ suc (fst p) , PT.rec nFinite-isProp (λ x → ∣ (fst x) , (fst (snd x)) ,
                        transport (λ i → isConnectedFun (+-suc (fst p) n i)
                                                         (fst (snd x)))
                                  (snd (snd x)) ∣₁) (snd p) ∣₁

susp-stablyNFinite : (n : HLevel) (A : Pointed ℓ)
  → stablyNFinite n A → stablyNFinite (suc n) (S∙ A)
susp-stablyNFinite n A = PT.rec squash₁
  (uncurry λ m → PT.rec squash₁
    (uncurry λ X → uncurry λ f c
      → ∣ (m , ∣ ((_ , isFinCWSusp {n = 1}
        (fst X) (snd X))
        , transport (p m) ∘ suspFun f
        , isConnectedComp (transport (p m))
           (suspFun f) (m + suc n)
           (isEquiv→isConnected _
             (transpEquiv (λ i → p m i) i0 .snd) _)
           (subst (λ k → isConnectedFun k (suspFun f))
                  (sym (+-suc m n))
                  (isConnectedSuspFun f _ c))) ∣₁) ∣₁))
  where
  p : (m : _) → _ ≡ _
  p m = cong Susp (sym (Susp^'≡Susp^ m))
      ∙ Susp^'≡Susp^ (suc m)

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

joinSuspTrick : ∀ {ℓ} (X₁ X₂ : Pointed ℓ) (M₁ M₂ : ℕ)
  → Susp^ (M₁ + M₂) (join (fst X₁) (fst X₂))
   ≡ join (Susp^ M₁ (typ X₁)) (Susp^ M₂ (typ X₂))
joinSuspTrick X₁ X₂ zero zero = refl
joinSuspTrick X₁ X₂ zero (suc M₂) =
    cong (Susp^ M₂)
      (isoToPath
       (compIso (congSuspIso join-comm)
        (compIso (invIso (Iso-joinSusp-suspJoin {A = X₂} {X₁}))
         join-comm)))
  ∙ joinSuspTrick X₁ (Susp∙ (typ X₂)) zero M₂
joinSuspTrick X₁ X₂ (suc M₁) M₂ =
    sym (cong (Susp^ (M₁ + M₂))
              (isoToPath (Iso-joinSusp-suspJoin {A = X₁} {X₂})))
  ∙ joinSuspTrick (Susp∙ (X₁ .fst)) X₂ M₁ M₂
  ∙ cong₂ join refl refl

open import Cubical.HITs.Susp.SuspProduct
open import Cubical.HITs.SmashProduct

isFinCWSmash : (A B : Pointed ℓ) → {!isFinCW ?!}
isFinCWSmash = {!!}

safSusp→saf : {A : Pointed ℓ} → saf (S∙ A) → saf A
safSusp→saf sA m = {!!}
{-
  PT.rec squash₁
    (uncurry (λ n → PT.rec squash₁
      λ {(X , f , c) → ∣ (suc (suc n)) , ∣ ((_ , isFinCWSusp {n = 1} (typ X) (snd X)) , ({!!} ∘ suspFun f , {!!})) ∣₁ ∣₁}))
    (sA m)
-}

Iso-Smash-⋀ : ∀{ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
  → Iso (Smash A B) (A ⋀ B)
Iso-Smash-⋀ .Iso.fun = Smash→⋀
Iso-Smash-⋀ .Iso.inv = ⋀→Smash
Iso-Smash-⋀ {A = A} {B = B} .Iso.rightInv x =
  ⋀-fun≡ (Smash→⋀ ∘ ⋀→Smash) (idfun _)
    refl
    (λ _ → refl)
    (λ a i j → push (inl a) i)
    (λ x → flipSquare
            (cong-∙∙ Smash→⋀
              (sym (gluel (pt A))) (gluer (pt B)) (sym (gluer x))
            ∙ doubleCompPath≡compPath _ _ _
            ∙ assoc _ _ _
            ∙ cong₂ _∙_ (cong₂ _∙_ (λ j i → push (push tt j) i) refl
                       ∙ rCancel (push (inr (pt B)))) refl
            ∙ sym (lUnit (push (inr x))))) x
Iso-Smash-⋀ .Iso.leftInv basel = refl
Iso-Smash-⋀ {A = A} {B = B} .Iso.leftInv baser = sym (gluel (pt A)) ∙' gluer (pt B)
Iso-Smash-⋀ .Iso.leftInv (proj x y) = refl
Iso-Smash-⋀ .Iso.leftInv (gluel a i) = refl
Iso-Smash-⋀ {A = A} {B = B} .Iso.leftInv (gluer b i) j =
  hcomp (λ k → λ {(i = i0) → gluer b (~ k)
                 ; (j = i0) → doubleCompPath-filler
                                (sym (gluel (pt A))) (gluer (pt B)) (sym (gluer b)) k (~ i)
                 ; (j = i1) → gluer b (i ∨ ~ k)})
        (gluer (pt B) (~ i ∨ j))

⋀-fun≡Dep : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : A ⋀ B → Type ℓ''}
  → (f g : (x : A ⋀ B) → C x)
  → (p : f (inl tt) ≡ g (inl tt))
  → (h : (x : _) → f (inr x) ≡ g (inr x))
  → ((a : fst A) → SquareP (λ i j → C (push (inl a) j))
                            (cong f (push (inl a)))
                            (cong g (push (inl a)))
                            p (h (a , (pt B))))
  → ((b : fst B) → SquareP (λ i j → C (push (inr b) j))
                            (cong f (push (inr b)))
                            (cong g (push (inr b)))
                            p (h ((pt A) , b)))
  → (x : _) → f x ≡ g x 
⋀-fun≡Dep {A = A} {B} {C} f g p h pl pr x i =
  comp (λ k → C (Iso.rightInv Iso-Smash-⋀ x k))
       (λ k → λ {(i = i0) → f (Iso.rightInv Iso-Smash-⋀ x k)
                ; (i = i1) → g (Iso.rightInv Iso-Smash-⋀ x k)})
       (lem (⋀→Smash x) i)
  where
  lem : (x : Smash A B) → f (Smash→⋀ x) ≡ g (Smash→⋀ x)
  lem basel = p
  lem baser = p
  lem (proj x y) = h (x , y)
  lem (gluel a i) j = pl a j (~ i)
  lem (gluer b i) j = pr b j (~ i)

⋀→idfun' : ∀ {ℓ ℓ' ℓ''} (A : Pointed ℓ) {B : Type ℓ'} (C : Pointed ℓ'')
  (f : typ A → B) → A ⋀ C → (B , f (pt A)) ⋀ C
⋀→idfun' A C f (inl x) = inl tt
⋀→idfun' A C f (inr (x , y)) = inr (f x , y)
⋀→idfun' A C f (push (inl x) i) = push (inl (f x)) i
⋀→idfun' A C f (push (inr x) i) = push (inr x) i
⋀→idfun' A C f (push (push a i₁) i) = push (push a i₁) i

⋀→idfun'≡⋀→idfun : ∀ {ℓ ℓ' ℓ''} (A : Pointed ℓ) {B : Type ℓ'} {C : Pointed ℓ''}
  → (f : typ A → B) (x : A ⋀ C)
  → ((f , refl) ⋀→ idfun∙ C) x ≡ ⋀→idfun' A C f x 
⋀→idfun'≡⋀→idfun A {C = C} f =
  ⋀-fun≡ ((f , refl) ⋀→ idfun∙ _) (⋀→idfun' A C f)
    refl (λ _ → refl)
    (λ x → flipSquare (sym (rUnit (push (inl (f x))))))
    λ x → flipSquare (sym (rUnit (push (inr x))))

module ⋀ₗ→connected'-lemmas
  {ℓ ℓ' ℓ'' ℓ'''} {A : Pointed ℓ}
  {B' : Type ℓ'} {C : Pointed ℓ''} (f : typ A → B')
  (nC nf : ℕ) (P : (B' , f (pt A)) ⋀ C → TypeOfHLevel ℓ''' (predℕ (nC + nf)))
  (d : (x : _) → P ((⋀→idfun' A C f) x) .fst) where
  B : Pointed _
  B = B' , f (pt A)

  Q : fst C → Type _
  Q c = fiber {A = (k : fst B) → fst (P (inr (k , c)))}
               {B = (k : fst A) → fst (P (inr (f k , c)))}
               (_∘ f) (d ∘ λ a → inr (a , c))


  Q⋆ : Q (pt C)
  Q⋆ .fst b = subst (fst ∘ P) (push (inl b)) (d (inl tt))
  Q⋆ .snd i a = transp (λ j → fst (P ((push (inl (f a))) (i ∨ j))))
                     i (d (push (inl a) i))

  module _ (Q-full : (c : fst C) → Q c) (Q-fullβ : Q-full (pt C) ≡ Q⋆) where
    g : (b : fst B)(c : fst C) → P (inr (b , c)) .fst
    g b c = Q-full c .fst b

    gₗ : (a : fst A) (c : fst C)
      → g (f a) c ≡ d (inr (a , c))
    gₗ a c = funExt⁻ (Q-full c .snd) a

    gᵣ : (b : fst B)
      → g b (pt C) ≡ Q⋆ .fst b
    gᵣ b = funExt⁻ (cong fst Q-fullβ) b

    gₗ≡gᵣ : (a : fst A)
      → Square (gₗ a (pt C)) (gᵣ (f a))
                refl (sym (funExt⁻ (snd Q⋆) a))
    gₗ≡gᵣ a i j =
      hcomp (λ k → λ {(i = i0) → gₗ a (pt C) (j ∨ ~ k)
                     ; (i = i1) → gᵣ (f a) j
                     ; (j = i0) → gₗ a (pt C) (~ i ∧ ~ k)
                     ; (j = i1) → snd Q⋆ (~ i) a})
            (snd (Q-fullβ j) (~ i) a)

    r : (b : B ⋀ C) → P b .fst
    r (inl x) = d (inl tt)
    r (inr (x , c)) = g x c
    r (push (inl x) i) =
      ((λ j → transp (λ k → fst (P (push (inl x) (j ∧ k)))) (~ j) (d (inl tt)))
      ▷ (sym (gᵣ x))) i
    r (push (inr x) i) = (cong d (push (inr x)) ▷ sym (gₗ (pt A) x)) i
    r (push (push a j) i) = lem j i
      where
      lem : SquareP (λ i j → P (push (push a i) j) .fst)
                    ((λ j → transp (λ k → fst (P (push (inl (f (pt A)))
                                    (j ∧ k)))) (~ j) (d (inl tt)))
                    ▷ sym (gᵣ (pt B)))
                    ((cong d (push (inr (pt C)))
                    ▷ sym (gₗ (pt A) (pt C))))
                    refl
                    refl
      lem i =
          (λ j → comp
            (λ k → P (push (push a (i ∧ k)) j) .fst)
            (λ k → λ {(i = i0) →
              transp (λ k → fst (P (push (inl (f (pt A))) (j ∧ k))))
                     (~ j) (d (inl tt))
                    ; (i = i1) → d (push (push tt k) j)
                    ; (j = i0) → d (inl tt)
                    ; (j = i1) →
              transp (λ k → fst (P (push (inl (f (pt A)))
                                      (i ∨ k)))) i
                       (d (push (inl (pt A)) i))})
                  (transp (λ k → fst (P (push (inl (f (snd A)))
                                          ((i ∨ k) ∧ j)))) (i ∨ ~ j)
                          (d (push (inl (snd A)) (i ∧ j)))))
        ▷ sym (gₗ≡gᵣ (pt A) (~ i))

    secP : r ∘ ⋀→idfun' A C f ≡ d
    secP = funExt
      (⋀-fun≡Dep (r ∘ (⋀→idfun' A C f)) d
        refl
        (λ x → gₗ (fst x) (snd x))
        (λ a i j → hcomp (λ k →
          λ {(i = i0) → cong (λ x → r (⋀→idfun' A C f x)) (push (inl a)) j
           ; (i = i1) → transp (λ r → fst (P (push (inl (f a))
                                              (j ∧ (r ∨ k)))))
                                (~ j ∨ k) (d (push (inl a) (j ∧ k)))
           ; (j = i0) → d (inl tt)
           ; (j = i1) → gₗ≡gᵣ a (~ k) i})
           (doubleWhiskFiller refl
             (λ j → transp (λ k → fst (P (push (inl (f a)) (j ∧ k))))
                            (~ j) (d (inl tt)))
                (sym (gᵣ (f a))) (~ i) j))
        (λ a i j → hcomp (λ k →
          λ {(i = i1) → d (push (inr a) j)
           ; (j = i0) → d (inl tt)
           ; (j = i1) → gₗ (pt A) a (i ∨ ~ k)})
          (d (push (inr a) j))))

asd = toProdIso

⋀ₗ→connected' : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ}
  {B : Type ℓ'} {C : Pointed ℓ''} (nf nC : ℕ)
  → isConnected nC (fst C)
  → (f : typ A → B)
  → isConnectedFun nf f
  → isConnectedFun (predℕ (nC + nf)) (⋀→idfun' A C f)
⋀ₗ→connected' {A = A} {B = B'} {C = C} zero zero cC f cf =
  λ b → tt* , (λ y i → tt*)
⋀ₗ→connected' {A = A} {B = B'} {C = C} (suc nf) zero cC f cf =
  elim.isConnectedPrecompose (⋀→idfun' A C f) nf
    λ P → (λ d → r P d (Q-full P d) (Q-fullβ P d))
    , λ d → secP P d (Q-full P d) (Q-fullβ P d)
  where
  module _
    {ℓ} (P : (B' , f (pt A)) ⋀ C
       → TypeOfHLevel ℓ nf) (d : (x : _) → P (⋀→idfun' A C f x) .fst) where

    open ⋀ₗ→connected'-lemmas {A = A} {B'} {C} f 0 (suc nf) P d public

    hLevQ : (c' : fst C) → isOfHLevel zero (Q c')
    hLevQ c' = isOfHLevelPrecomposeConnected zero nf
      (λ b → P (inr (b , c'))) f (isConnectedFunSubtr nf 1 f cf)
        λ x → d (inr (x , c'))

    Q-full : (c : fst C) → Q c
    Q-full c = fst (hLevQ c)

    Q-fullβ : Q-full (pt C) ≡ Q⋆
    Q-fullβ = snd (hLevQ (pt C)) Q⋆
⋀ₗ→connected' {A = A} {B = B'} {C = C} nf (suc nC) cC f cf =
  elim.isConnectedPrecompose (⋀→idfun' A C f) (nC + nf)
    λ P → (λ d → r P d (Q-full P d) (Q-fullβ P d))
    , λ d → secP P d (Q-full P d) (Q-fullβ P d)
  where
  module _
    {ℓ} (P : (B' , f (pt A)) ⋀ C
       → TypeOfHLevel ℓ (nC + nf)) (d : (x : _) → P (⋀→idfun' A C f x) .fst) where

    open ⋀ₗ→connected'-lemmas {A = A} {B'} {C} f (suc nC) nf P d public

    hLevQ : (c' : fst C) → isOfHLevel nC (Q c')
    hLevQ c' =
      isOfHLevelPrecomposeConnected nC (nf)
        (λ b → P (inr (b , c'))) f cf λ x → d (inr (x , c'))

    Q-full : (c : fst C) → Q c 
    Q-full =
      Iso.inv (elim.isIsoPrecompose (λ _ → pt C)
              nC
              (λ t → Q t , hLevQ t)
              (isConnectedPoint _ cC (pt C)))
              (λ _ → Q⋆)

    Q-fullβ : Q-full (pt C) ≡ Q⋆
    Q-fullβ =
      elim.isIsoPrecomposeβ (λ _ → pt C)
              nC
              (λ t → Q t , hLevQ t)
              (isConnectedPoint _ cC (pt C))
              (λ _ → Q⋆) tt

module _ {ℓA ℓB ℓC ℓD ℓE ℓF}
  {A : Pointed ℓA} {B : Pointed ℓB}
  {C : Pointed ℓC} {D : Pointed ℓD}
  {E : Pointed ℓE} {F : Pointed ℓF}
  (f : A →∙ B) (g : C →∙ D)
  (h : B →∙ E) (k : D →∙ F)
  where
  ⋀→comp : (x : _) → (h ⋀→ k) ((f ⋀→ g) x)
                    ≡ ((h ∘∙ f) ⋀→ (k ∘∙ g)) x
  ⋀→comp = ⋀-fun≡ _ _ refl (λ _ → refl)
    (λ x → flipSquare (cong-∙ (h ⋀→ k)
                (push (inl (fst f x))) (λ i → inr (fst f x , snd g (~ i)))
              ∙ sym (assoc _ _ _)
              ∙ sym (cong₂ _∙_ refl (cong-∙∙ (λ t → inr (h .fst (fst f x) , t))
                             (sym (snd k))
                             (λ i → k .fst (g .snd (~ i)))
                             λ _ → k .fst (g .fst (C .snd)))
              ∙ cong₂ _∙_ refl
                      (sym (compPath≡compPath' _ _)))))
    λ x → flipSquare (cong-∙ (h ⋀→ k)
             (push (inr (fst g x)))
             (λ i → inr (snd f (~ i) , fst g x))
           ∙ sym (assoc _ _ _)
           ∙ cong₂ _∙_ refl (compPath≡compPath' _ _)
           ∙ sym (cong₂ _∙_ refl
                  (cong-∙∙ (λ t → inr (t , k .fst (fst g x)))
                           (sym (snd h))
                           (cong (fst h) (sym (snd f)))
                           refl)))

isConnectedFunCompMin : ∀ {ℓA ℓB ℓC}
  {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
  (n m : ℕ) (f : A → B) (g : B → C)
  → isConnectedFun n f → isConnectedFun m g
  → isConnectedFun (min n m) (g ∘ f)
isConnectedFunCompMin n m f g cf cg =
  isConnectedComp g f (min n m)
    (isConnectedFunSubtr (min n m)
      (fst (min-≤-left {m = m} {n})) _
    (subst (λ k → isConnectedFun k g)
      (sym (snd (min-≤-left {m = m} {n}))
      ∙ cong (fst (min-≤-left {m = m} {n}) +_)
            (minComm m n)) cg))
    (isConnectedFunSubtr (min n m)
      (fst (min-≤-left {m = n} {m})) _
    (subst (λ k → isConnectedFun k f)
      (sym (snd (min-≤-left {m = n} {m}))) cf))

⋀ₗ→connected : ∀ {ℓA ℓB ℓC}
  {A : Pointed ℓA} {B : Pointed ℓB}
  {C : Pointed ℓC} (nf nC : ℕ)
  → isConnected nC (fst C)
  → (f : A →∙ B)
  → isConnectedFun nf (fst f)
  → isConnectedFun (predℕ (nC + nf)) (f ⋀→ idfun∙ C)
⋀ₗ→connected {A = A} {B = B , b} {C} nf nC cC =
  uncurry λ f p cf
    → J (λ b p → isConnectedFun (predℕ (nC + nf)) ((f , p) ⋀→ idfun∙ C))
        (transport (λ i → isConnectedFun (predℕ (nC + nf))
                           (λ x → ⋀→idfun'≡⋀→idfun A {C = C} f x (~ i)))
          (⋀ₗ→connected' nf nC cC f cf)) p

open import Cubical.HITs.SmashProduct.SymmetricMonoidal

⋀ᵣ→connected : {A B C  : Pointed ℓ} (nf nC : ℕ)
  → isConnected nC (fst C)
  → (f : A →∙ B)
  → isConnectedFun nf (fst f)
  → isConnectedFun (predℕ (nC + nf)) (idfun∙ C ⋀→ f)
⋀ᵣ→connected {C = C} nf nC x f cf =
  subst (isConnectedFun (predℕ (nC + nf)))
    (sym (cong fst (⋀comm-sq' (idfun∙ _) f)))
    (isConnectedComp ⋀comm→ ((f ⋀→ idfun∙ _) ∘ ⋀comm→)
      (predℕ (nC + nf))
      (isEquiv→isConnected _ (isoToIsEquiv ⋀CommIso) (predℕ (nC + nf)))
       (isConnectedComp (f ⋀→ idfun∙ _) ⋀comm→ (predℕ (nC + nf))
         (⋀ₗ→connected nf nC x f cf)
             (isEquiv→isConnected _ (isoToIsEquiv ⋀CommIso) _)))

isConnected⋀→ :
  {A B C D : Pointed ℓ} (nf ng nC nB : ℕ)
  → isConnected nC (fst C)
  → isConnected nB (fst B)
  → (f : A →∙ B) (g : C →∙ D)
  → isConnectedFun nf (fst f)
  → isConnectedFun ng (fst g)
  → isConnectedFun (min (predℕ (nC +  nf)) (predℕ (nB + ng))) (f ⋀→ g)
isConnected⋀→ nf ng nC nB cC cD f g cf cg =
  subst (isConnectedFun (min (predℕ (nC + nf)) (predℕ (nB + ng))))
     (funExt (λ x → ⋀→comp f (idfun∙ _) (idfun∙ _) g x
           ∙ cong₂ (λ f g → (f ⋀→ g) x) (∘∙-idʳ f) (∘∙-idˡ g)))
     (isConnectedFunCompMin (predℕ (nC + nf)) (predℕ (nB + ng))
       (f ⋀→ idfun∙ _) (idfun∙ _ ⋀→ g)
       (⋀ₗ→connected nf nC cC f cf)
       (⋀ᵣ→connected ng nB cD g cg))

isConnectedSusp^ : {X : Type ℓ} (n m : HLevel)
  → isConnected n X → isConnected (m + n) ((Susp^ m) X)
isConnectedSusp^ n zero cX = cX
isConnectedSusp^ {X = X} n (suc m) cX =
  subst (isConnected (suc (m + n))) (sym (Susp^-comm m X))
    (isConnectedSusp (m + n) (isConnectedSusp^ n m cX))

Susp^∙ : ℕ → Pointed ℓ → Pointed ℓ
Susp^∙ n x .fst = Susp^ n (typ x)
Susp^∙ zero x .snd = pt x
Susp^∙ (suc n) x .snd = Susp^∙ n (Susp∙ (typ x)) .snd

Susp^Equiv∙ : {A B : Pointed ℓ} (n : ℕ)
  → A ≃∙ B →  Susp^∙ n A ≃∙ Susp^∙ n B 
Susp^Equiv∙ zero e = e
Susp^Equiv∙ (suc n) e = Susp^Equiv∙ n (congSuspEquiv (fst e) , refl)

-- Susp^'≡Susp^ : (n : ℕ) {A : Type ℓ} → Susp^'∙ n A ≡ Susp^∙ n A

Susp^SmashEquiv∙ : (A B : Pointed ℓ) (nA nB : ℕ)
  →  (Susp^∙ (nA + nB) (A ⋀∙ B))
   ≃∙ ((Susp^∙ nA A) ⋀∙ (Susp^∙ nB B))
Susp^SmashEquiv∙ A B zero zero = idEquiv∙ _
Susp^SmashEquiv∙ A B zero (suc nB) =
  compEquiv∙ (Susp^Equiv∙ nB
    ((compEquiv∙ ((congSuspEquiv (isoToEquiv ⋀CommIso)) , refl)
                 (compEquiv∙ (invEquiv (isoToEquiv (SuspSmashCommIso {A = B} {A}))
                 , refl)
                 ((isoToEquiv ⋀CommIso) , refl)))))
     (Susp^SmashEquiv∙ A (Susp∙ (typ B)) zero nB)
Susp^SmashEquiv∙ A B (suc nA) nB =
  compEquiv∙ (Susp^Equiv∙ (nA + nB)
    (isoToEquiv (invIso SuspSmashCommIso) , refl))
    (Susp^SmashEquiv∙ (Susp∙ (typ A)) B nA nB)

open import Cubical.HITs.Wedge
module _ {ℓ} {A B : Pointed ℓ} (cwA : isFinCW (typ A)) (cwB : isFinCW (typ B)) where
  private
    A⋁B' = Pushout {A = Unit* {ℓ = ℓ}} (λ _ → pt A) (λ _ → pt B)

    A⋁B'≅A⋁B : A⋁B' ≃ (A ⋁ B)
    A⋁B'≅A⋁B = invEquiv (pushoutEquiv _ _ _ _ LiftEquiv (idEquiv _) (idEquiv _) refl refl)

    A⋀B' = Pushout {A = A⋁B'} {B = Unit* {ℓ = ℓ}} (λ _ → tt*) (⋁↪ ∘ fst A⋁B'≅A⋁B)

    A⋀B'≃A⋀B : A⋀B' ≃ (A ⋀ B)
    A⋀B'≃A⋀B = pushoutEquiv _ _ _ _ A⋁B'≅A⋁B (invEquiv LiftEquiv) (idEquiv _) refl refl

  isFinCW⋁ : isFinCW (A ⋁ B)
  isFinCW⋁ = subst isFinCW (sym lem)
                   (isFinCWPushout _ _ isFinCWUnit cwA cwB)
    where
    lem : A ⋁ B ≡ Pushout {A = Unit* {ℓ = ℓ}} (λ _ → pt A) (λ _ → pt B)
    lem = ua (pushoutEquiv _ _ _ _ LiftEquiv (idEquiv _) (idEquiv _) refl refl)

  isFinCW⋀ : isFinCW (A ⋀ B)
  isFinCW⋀ = subst isFinCW (sym lem⋀)
                   (isFinCWPushout _ _ isFinCW⋁ isFinCWUnit (isFinCW× (_ , cwA) (_ , cwB)))
    where
    lem⋀ : A ⋀ B ≡ Pushout {A = A ⋁ B} {B = Unit* {ℓ = ℓ}} (λ _ → tt*) ⋁↪
    lem⋀ = ua (pushoutEquiv _ _ _ _ (idEquiv _) LiftEquiv (idEquiv _) refl refl)



isConnectedCodomain : ∀ {ℓ} {A B : Type ℓ}  (n m : ℕ) (f : A → B)
  → isConnected n B
  → isConnectedFun (m + n) f
  → isConnected n A
isConnectedCodomain n m f cA cf =
  isOfHLevelRespectEquiv zero
    (invEquiv (connectedTruncEquiv n f
      (λ b → isConnectedSubtr n m (cf b))))
      cA

Susp∙^Susp≡Susp^Susp∙ : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → Susp∙ (Susp^ n (typ A)) ≡ Susp^∙ n (Susp∙ (typ A))
Susp∙^Susp≡Susp^Susp∙ {A = A} zero = refl
Susp∙^Susp≡Susp^Susp∙ {A = A} (suc n) =
  Susp∙^Susp≡Susp^Susp∙ {A = Susp∙ (typ A)} n

min-diag : (a : ℕ) → min a a ≡ a
min-diag zero = refl
min-diag (suc a) = cong suc (min-diag a)

saf⋀ : {A B : Pointed ℓ} → saf A → saf B → saf (A ⋀∙ B)
saf⋀ {ℓ = ℓ} {A = A} {B = B} sA sB m =
  PT.rec2 squash₁
    (uncurry (λ nA → PT.rec (isPropΠ (λ _ → squash₁))
      λ {(XA , f , cf)
      → uncurry (λ nB → PT.rec squash₁
      λ{(XB , g , cg)
        → main m nA nB XA XB f g
              (subst (λ k → isConnectedFun k f) (+-comm nA m) cf)
              (subst (λ k → isConnectedFun k g) (+-comm nB m) cg)})}))
    (sA m) (sB m)
  where
  main : (m nA nB : ℕ) (XA XB : FinCW ℓ)
    (f : fst XA → Susp^ nA (typ A))
    (g : fst XB → Susp^ nB (typ B))
    (cf : isConnectedFun (m + nA) f)
    (cg : isConnectedFun (m + nB) g)
    → stablyNFinite m (A ⋀∙ B)
  main zero nA nB XA XB f g cf cg =
    ∣ 0 , ∣ (_ , isFinCWUnit)
        , ((λ _ → inl tt) , (λ b → tt* , λ _ → refl)) ∣₁ ∣₁
  main (suc m) nA nB XA XB f g cf cg =
    TR.rec (isProp→isOfHLevelSuc (m + nA) squash₁)
      (λ {(x , xId)
      → TR.rec (isProp→isOfHLevelSuc (m + nB) squash₁)
        (λ {(y , yId) → ∣ ((nA + nB) , ∣
          ((((fst XA , x)) ⋀ ((fst XB , y))
          , isFinCW⋀ ((snd XA)) (snd XB))
          , (invEq (fst (Susp^SmashEquiv∙ A B nA nB))
          ∘ ((f , xId) ⋀→ (g , yId)))
          , isConnectedComp
               (invEq (fst (Susp^SmashEquiv∙ A B nA nB)))
               ((f , xId) ⋀→ (g , yId))
            (nA + nB + suc m)
            (isEquiv→isConnected _
              (snd (invEquiv (fst (Susp^SmashEquiv∙ A B nA nB)))) _)
            (subst (λ k → isConnectedFun k ((f , xId) ⋀→ (g , yId)))
              (cong₂ min
                (cong (nB +_) (+-comm (suc m) nA)
                ∙ +-assoc nB nA (suc m)
                ∙ cong (_+ suc m) (+-comm nB nA))
                (cong (nA +_) (+-comm (suc m) nB)
                ∙ +-assoc nA nB (suc m)) ∙ min-diag (nA + nB + suc m))
              (isConnected⋀→ (suc (m + nA)) (suc (m + nB)) (suc nB) (suc nA)
                conXB conSuspXA (f , xId) (g , yId) cf cg))) ∣₁) ∣₁})
        (cg (Susp^∙ nB B .snd) .fst)})
      (cf (Susp^∙ nA A .snd) .fst)
        where
        conSuspXA : isConnected (suc nA) (Susp^ nA (typ A))
        conSuspXA = subst (λ r → isConnected r (Susp^ nA (typ A)))
                     (+-comm nA 1)
                     (isConnectedSusp^ (suc zero) nA
                       (∣ pt A ∣ , (isOfHLevelTrunc 1 ∣ (pt A) ∣)))

        conXB : isConnected (suc nB) (fst XB)
        conXB = isConnectedCodomain (suc nB) m g
                   (subst (λ r → isConnected r (Susp^ nB (typ B)))
                     (+-comm nB 1)
                     (isConnectedSusp^ (suc zero) nB
                       (∣ pt B ∣ , (isOfHLevelTrunc 1 ∣ (pt B) ∣))))
                       (subst (λ k → isConnectedFun k g) (sym (+-suc m nB)) cg)

saf× : {A B : Pointed ℓ} → saf A → saf B → saf (A ×∙ B)
saf× sA sB m =
  PT.rec2 squash₁
    (uncurry
      (λ nA → PT.rec (isPropΠ λ _ → squash₁)
      λ {(XA , f , cf) →
      uncurry (λ nB → PT.rec squash₁
        λ {(XB , g , cg)
        → ∣ {!!} , {!!} ∣₁})}))
    (sA m) (sB m)

safS¹× : {A : Pointed ℓ} → saf A → saf (S¹∙ ×∙ A)
safS¹× = {!!}

safS1× : {A : Pointed ℓ} → saf A → saf ((S {ℓ} 1) ×∙ A)
safS1× = {!!}

stablyNFiniteJoin'-alt : {X₁ X₂ : Pointed ℓ} (m₁ m₂ n₂ : HLevel)
  (hXm₁ : isConnected (m₁ + 2) (typ X₁)) (hX₁ : stablyNFinite' 1 X₁)
  (hXm₂ : isConnected m₂ (typ X₂)) (hXn₂ : stablyNFinite' n₂ X₂)
  (k : HLevel) (hk₁ : k ≤ 1 + m₂) (hk₂ : k ≤ n₂ + (m₁ + 2))
  → stablyNFinite' k (join∙ X₁ X₂)
stablyNFiniteJoin'-alt {ℓ} {X₁} {X₂} m₁ m₂ n₂ hXm₁ hX₁ hXm₂ hXn₂ k hk₁ hk₂ =
  γ α
  where


    -- notice, the following construction is only possible because X₁ is pointed
    -- we could weaken this hypothesis
    -- but then we would only have an `α' up to propositional truncation
    α : (Σ[ m ∈ ℕ ] (Σ[ C ∈ FinCW ℓ ]
     Σ[ f ∈ (decodeFinCW C → (Susp^ m (typ X₁))) ]
     (isConnectedFun (m + 1) f) × (isConnected (m + (m₁ + 2)) (decodeFinCW C))))
    fst α = 0
    fst (snd α) = Unit* , isFinCWUnit
    fst (snd (snd α)) = λ _ → pt X₁
    fst (snd (snd (snd α))) = isConnectedPoint* 1 (isConnectedSubtr 2 m₁ hXm₁) (pt X₁)
    snd (snd (snd (snd α))) = isConnectedUnit* (m₁ + 2)


    β : (Σ[ m ∈ ℕ ] (Σ[ C ∈ FinCW ℓ ]
     Σ[ f ∈ (decodeFinCW C → (Susp^ m (typ X₁))) ]
     (isConnectedFun (m + 1) f) × (isConnected (m + (m₁ + 2)) (decodeFinCW C))))
      → (Σ[ m ∈ ℕ ] (Σ[ C ∈ FinCW ℓ ]
     Σ[ f ∈ (decodeFinCW C → (Susp^ m (typ X₂))) ]
     isConnectedFun (m + n₂) f))
      → stablyNFinite' k (join∙ X₁ X₂)
    β (M₁ , C₁ , f₁ , cf₁ , cC₁) (M₂ , C₂ , f₂ , cf₂) =
      ∣ (M₁ + M₂)
       , (((join (typ C₁) (typ C₂))
       , (isFinCWJoin (snd C₁) (snd C₂)))
       , (transport (λ i → join (typ C₁) (typ C₂)
                                → joinSuspTrick X₁ X₂ M₁ M₂ (~ i)) (join→ f₁ f₂))
       , isConnectedTrnspConnected (sym (joinSuspTrick X₁ X₂ M₁ M₂)) (join→ f₁ f₂)
           (isConnectedFunJoin f₁ f₂ (M₁ + 1) (M₂ + n₂)
              (M₁ + (m₁ + 2)) (M₂ + m₂) (M₁ + M₂ + k)
              (arithmetric M₁ M₂ k 1 m₂ hk₁)
              (arithmetric' M₂ M₁ k n₂ (m₁ + 2) hk₂)
              cf₁ cf₂ cC₁ (Susp^-conn m₂ M₂ (typ X₂) hXm₂))) ∣₁

    γ : (Σ[ m ∈ ℕ ] (Σ[ C ∈ FinCW ℓ ]
     Σ[ f ∈ (decodeFinCW C → (Susp^ m (typ X₁))) ]
     (isConnectedFun (m + 1) f) × (isConnected (m + (m₁ + 2)) (decodeFinCW C))))
        → stablyNFinite' k (join∙ X₁ X₂)
    γ hX₁ = PT.rec (stablyNFinite'-isProp {ℓ} {k} {join∙ X₁ X₂})
                   (β hX₁)
                   hXn₂



-- If Xᵢ is stably (nᵢ-1)-finite and (mᵢ-2)-connected (i = 1, 2)
-- then the join X₁ * X₂ is stably min(n₁+m₂-1, n₂+m₁-1)-connected
-- provided that m₁ ≤ n₁ (i.e., that m₁-2 < n₁-1).
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
    arithmetic : (M₁ : ℕ) → (a + (M₁ + m₁)) ≡ (M₁ + n₁)
    arithmetic M₁ = cong (a +_) (+-comm M₁ m₁)
                 ∙ +-assoc a m₁ M₁
                 ∙ cong (_+ M₁) p
                 ∙ +-comm n₁ M₁

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
                      (transport (λ i → isConnectedFun (arithmetic M₁ (~ i)) f) cf)))

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
                                → joinSuspTrick X₁ X₂ M₁ M₂ (~ i)) (join→ f₁ f₂)
               , isConnectedTrnspConnected (sym (joinSuspTrick X₁ X₂ M₁ M₂))
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

stablyNFiniteJoin-alt : {X₁ X₂ : Pointed ℓ} (m₁ m₂ n₂ : HLevel)
  (hXm₁ : isConnected (m₁ + 2) (typ X₁)) (hX₁ : stablyNFinite 1 X₁)
  (hXm₂ : isConnected m₂ (typ X₂)) (hXn₂ : stablyNFinite n₂ X₂)
  (k : HLevel) (hk₁ : k ≤ 1 + m₂) (hk₂ : k ≤ n₂ + (m₁ + 2))
  → stablyNFinite k (join∙ X₁ X₂)
stablyNFiniteJoin-alt {ℓ} {X₁} {X₂} m₁ m₂ n₂ hXm₁ hX₁ hXm₂ hXn₂ k hk₁ hk₂ =
  stablyNFinite'→stablyNFinite {X = join∙ X₁ X₂}
   (stablyNFiniteJoin'-alt {ℓ} {X₁} {X₂} m₁ m₂ n₂ hXm₁
     (stablyNFinite→stablyNFinite' {X = X₁} hX₁) hXm₂
     (stablyNFinite→stablyNFinite' {X = X₂} hXn₂) k hk₁ hk₂)

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


srthmetic : (m n : ℕ) → (m + suc n) ≡ (suc (m + n))
srthmetic m n = +-suc m n

stablyNFiniteApprox : {X Y : Pointed ℓ} (f : X →∙ Y)
    (n : HLevel) (hf : isConnectedFun n (fst f))
    → stablyNFinite n X → stablyNFinite n Y
stablyNFiniteApprox f n hf hX =
  PT.rec squash₁ (λ hX' → ∣ (fst hX') ,
  (nFiniteApprox (Susp→^ (fst hX') (fst f))
  (fst hX' + n)
  (Susp→^-conn (fst hX') n (fst f) hf)
  (snd hX')) ∣₁) hX



stablyNFiniteDrop : {X : Pointed ℓ} (n : HLevel)
    → stablyNFinite (1 + n) X → stablyNFinite n X
stablyNFiniteDrop {X = X} n =
  PT.rec (stablyNFinite-isProp {n = n} {X = X})
         λ hX → ∣ (fst hX) ,
                  nFiniteDrop (fst hX + n)
                  (transport (λ i → nFinite (srthmetic (fst hX) n i) (Susp^ (fst hX) (typ X))) (snd hX)) ∣₁

stablyNFiniteLower : {X : Pointed ℓ} (m n : HLevel)
  → stablyNFinite (m + n) X → stablyNFinite n X
stablyNFiniteLower zero n hX = hX
stablyNFiniteLower {X = X} (suc m) n hX =
  stablyNFiniteLower {X = X} m n (stablyNFiniteDrop {X = X} (m + n) hX)

stablyNFiniteApprox' : {X Y : Pointed ℓ} (f : X →∙ Y)
    (n : HLevel) (hf : isConnectedFun (1 + n) (fst f))
    → stablyNFinite n Y → stablyNFinite n X
stablyNFiniteApprox' {ℓ} {X} {Y} f n cf hY =
  PT.rec squash₁ (λ hY' → ∣ γ hY' ∣₁) hY
  where
    drthmtc : (m n : ℕ) → (m + (1 + n)) ≡ (1 + (m + n))
    drthmtc m n = +-suc m n

    susp-f : (m : ℕ) → Susp^ m (typ X) → Susp^ m (typ Y)
    susp-f m = Susp→^ m (fst f)

    susp-f-conn : (m : ℕ) → isConnectedFun (1 + (m + n)) (susp-f m)
    susp-f-conn m = transport (λ i → isConnectedFun (drthmtc m n i) (susp-f m))
                              (Susp→^-conn m (1 + n) (fst f) cf)

    γ : (hY' : Σ[ m ∈ ℕ ] nFinite (m + n) (Susp^ m (typ Y)))
       → Σ[ m ∈ ℕ ] nFinite (m + n) (Susp^ m (typ X))
    γ (m , hY') = m , nFiniteApprox' (susp-f m) (m + n) (susp-f-conn m) hY'
