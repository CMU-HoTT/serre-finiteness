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
open import Cubical.HITs.Truncation
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Susp
open import Cubical.HITs.Sn hiding (S)
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.CW.Base
--open import Cubical.HITs.Sphere
open import Cubical.Algebra.AbGroup.Instances.Int renaming (ℤAbGroup to ℤ)

open import FiniteCW
open import PointedHITs
open import FPAbGroup
open import HomotopyGroups

open import FiberOrCofiberSequences.Base
open import FiberOrCofiberSequences.CofiberBase

open import Connectedness

open import AxelStuff.EM

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


-- silly postulates
isEquivTrnspId : {X Y : Type ℓ} (p : X ≡ Y)
  → isEquiv (transport (λ i → p i → X) (λ x → x))
isEquivTrnspId {X = X} p =
  transport (λ j → isEquiv (transp (λ i → p (i ∧ j) → X)
                                    (~ j) (λ x → x)))
    (idIsEquiv X)

postulate
  isConnectedUnit* : (n : ℕ) → isConnected n (Unit* {ℓ})

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

postulate
  susp-nFinite : {X : Type ℓ} (n : ℕ) → nFinite n X → nFinite (suc n) (Susp X)

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

postulate
  -- silly
  saf-Fin : ∀ n (b : Fin n) → saf (Fin n , b)

  saf-Unit : saf {ℓ} (Unit* , tt*)


  EM₁ℤ : (EM∙ {ℓ-zero} ℤ 1) ≡ S 1

  saf-Sn : ∀ n → saf (S {ℓ} n)

-- all just arithmetic
stablyNFiniteOfSusp : (n : HLevel) (A : Pointed ℓ)
      → stablyNFinite (suc n) (S∙ A) → stablyNFinite n A
stablyNFiniteOfSusp n A = PT.rec (stablyNFinite-isProp {X = A})
  λ p → ∣ suc (fst p) , PT.rec nFinite-isProp (λ x → ∣ (fst x) , (fst (snd x)) ,
                        transport (λ i → isConnectedFun (+-suc (fst p) n i)
                                                         (fst (snd x)))
                                  (snd (snd x)) ∣₁) (snd p) ∣₁

postulate
  susp-stablyNFinite : (n : HLevel) (A : Pointed ℓ)
    → stablyNFinite n A → stablyNFinite (suc n) (S∙ A) 

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

stablyNFiniteJoin'-alt : {X₁ X₂ : Pointed ℓ} (m₁ m₂ n₂ : HLevel)
  (hXm₁ : isConnected (m₁ + 2) (typ X₁)) (hX₁ : stablyNFinite' 1 X₁)
  (hXm₂ : isConnected m₂ (typ X₂)) (hXn₂ : stablyNFinite' n₂ X₂)
  (k : HLevel) (hk₁ : k ≤ 1 + m₂) (hk₂ : k ≤ n₂ + (m₁ + 2))
  → stablyNFinite' k (join∙ X₁ X₂)
stablyNFiniteJoin'-alt {ℓ} {X₁} {X₂} m₁ m₂ n₂ hXm₁ hX₁ hXm₂ hXn₂ k hk₁ hk₂ =
  γ α
  where
    postulate
      

      joinSuspTrick : (M₁ M₂ : ℕ) → Susp^ (M₁ + M₂) (join (fst X₁) (fst X₂))
                                     ≡ join (Susp^ M₁ (typ X₁))
                                            (Susp^ M₂ (typ X₂))

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
                                → joinSuspTrick M₁ M₂ (~ i)) (join→ f₁ f₂))
       , isConnectedTrnspConnected (sym (joinSuspTrick M₁ M₂)) (join→ f₁ f₂)
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
    postulate
      joinSuspTrick : (M₁ M₂ : ℕ) → Susp^ (M₁ + M₂) (join (fst X₁) (fst X₂))
                                     ≡ join (Susp^ M₁ (typ X₁))
                                            (Susp^ M₂ (typ X₂))

      -- p : a + m₁ ≡ n₁
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

postulate
  srthmetic : (m n : ℕ) → (m + suc n) ≡ (suc (m + n))

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
    postulate
      drthmtc : (m n : ℕ) → (m + (1 + n)) ≡ (1 + (m + n))
      
    susp-f : (m : ℕ) → Susp^ m (typ X) → Susp^ m (typ Y)
    susp-f m = Susp→^ m (fst f)

    susp-f-conn : (m : ℕ) → isConnectedFun (1 + (m + n)) (susp-f m)
    susp-f-conn m = transport (λ i → isConnectedFun (drthmtc m n i) (susp-f m))
                              (Susp→^-conn m (1 + n) (fst f) cf)

    γ : (hY' : Σ[ m ∈ ℕ ] nFinite (m + n) (Susp^ m (typ Y)))
       → Σ[ m ∈ ℕ ] nFinite (m + n) (Susp^ m (typ X))
    γ (m , hY') = m , nFiniteApprox' (susp-f m) (m + n) (susp-f-conn m) hY'
