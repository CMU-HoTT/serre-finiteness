{- 
   This is a summary file to accompany the paper

   A computer formalisation of the Serre finiteness theorem
-}

{-# OPTIONS --safe #-}

module Summary where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence

open import Cubical.Algebra.Group

open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool hiding (_≤_)
open import Cubical.Data.Sigma

open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Freudenthal
open import Cubical.Homotopy.Loopspace

open import Cubical.HITs.Sn hiding (S)
open import Cubical.HITs.Pushout
open import Cubical.HITs.Truncation
open import Cubical.HITs.Susp
open import Cubical.HITs.Join

variable
    ℓ : Level

open import SerreFinitenessTheorem

open import SAF

open import PointedHITs

open import HomotopyGroups

open import FPAbGroup

open import FiniteCW

open import CorollariesToHurewicz

open import CorollariesToGanea

open import Connectedness

open import LastMinuteLemmas.AlgebraLemmas
open import LastMinuteLemmas.ConnectedLemmas
open import LastMinuteLemmas.CWLemmas
open import LastMinuteLemmas.CWResize
open import LastMinuteLemmas.EM
open import LastMinuteLemmas.FinLemmas
open import LastMinuteLemmas.SmashLemmas
open import LastMinuteLemmas.Smith
open import LastMinuteLemmas.SuspLemmas

open import FiberOrCofiberSequences.Base
open import FiberOrCofiberSequences.ChainOfFibers
open import FiberOrCofiberSequences.CofiberBase
open import FiberOrCofiberSequences.LongExactSequence
open import FiberOrCofiberSequences.PuppeLemma
open import FiberOrCofiberSequences.ShortExact
open import FiberOrCofiberSequences.ShortExactSequence

open import ConnectedCovers.Base
open import ConnectedCovers.EMIsFiber
open import ConnectedCovers.EquivPreservation
open import ConnectedCovers.GeneralisingFreudnthl
open import ConnectedCovers.K-G-n-facts
open import ConnectedCovers.PointedEquivalences
open import ConnectedCovers.TruncationLevelFacts
open import ConnectedCovers.UsefulLemmas

-- Section 2 (Background)
N : Type₀
N = ℕ

𝟙 : Type₀
𝟙 = Unit

bot : Type₀
bot = ⊥

isEven' : N → Type₀
isEven' zero = 𝟙
isEven' (suc zero) = bot
isEven' (suc (suc x)) = isEven' x

divByEven : (n : N) → Σ[ m ∈ N ] Σ[ r ∈ N ] ((r < 2) × (2 · m + r ≡ n))
divByEven zero = 0 , (0 , ((≤-suc ≤-refl) , refl))
divByEven (suc zero) = 0 , (1 , (≤-refl , refl))
divByEven (suc (suc n)) = (suc (fst (divByEven n))) 
                        , (fst (snd (divByEven n))) 
                        , (fst (snd (snd (divByEven n)))) 
                        , (cong (_+ fst (snd (divByEven n))) (·-suc 2 (fst (divByEven n)))
                             ∙ +-assoc 2 (2 · fst (divByEven n)) (fst (snd (divByEven n))) 
                             ∙ cong (2 +_) (snd (snd (snd (divByEven n)))))

module _ (A B : Type₀) (f g : A → B) where

    rfl : (x : A) → x ≡ x
    rfl x = refl

    fnXt : ((x : A) → f x ≡ g x) → f ≡ g
    fnXt = funExt

𝕊¹ : Pointed₀
𝕊¹ = S₊∙ 1

module _ (A B C : Type₀) (f : A → B) (g : A → C) where

    Pshout : Type
    Pshout = Pushout f g

    univa : A ≃ B → A ≡ B
    univa = ua

    ua-not : Bool → Bool
    ua-not = transport (ua notEquiv)

    fibre-f : B → Type
    fibre-f b = fiber f b

    A≃B : Type
    A≃B = A ≃ B

    ∥A∥ : (n : N) → Type
    ∥A∥ n = ∥ A ∥ n

-- Proposition 2 (connectivity of composition)
Proposition-2 : {A B C : Type} (n : ℕ) (f : A → B) (g : B → C) → isConnectedFun n f → isConnectedFun n g → isConnectedFun n (g ∘ f)
Proposition-2 n f g cf cg = isConnectedComp g f n cg cf

-- Proposition 3 (connectivity cancelling on the right)
Proposition-3 : {A B C : Type} (n : ℕ) (f : A → B) (g : B → C) → isConnectedFun n f → isConnectedFun n (g ∘ f) → isConnectedFun n g
Proposition-3 zero f g cf cgf = λ b → isConnectedZero ⊥
Proposition-3 (suc n) f g cf cgf = isConnectedFunCancel f g n (isConnectedFunSubtr n 1 f cf) cgf

-- Proposition 4 (connectivity cancelling on the left)
Proposition-4 : {A B C : Type} (n : ℕ) (f : A → B) (g : B → C) → isConnectedFun (1 + n) g → isConnectedFun n (g ∘ f) → isConnectedFun n f
Proposition-4 n f g cg cgf = isConnectedFunCancel' f g n cg cgf

-- Definition 5 (Connected Covers)
Definition-5 : Pointed₀ → ℕ → Pointed₀
Definition-5 = _<_>

-- Definition 6 (homotopy groups)
Definition-6 : (n : ℕ) → Pointed₀ → Group₀
Definition-6 n = πGr n

-- Proposition 7 (Freudenthal)
Proposition-7 : (n : ℕ) (X : Pointed₀) → isConnected (2 + n) (fst X) → isConnectedFun (suc n + (suc n)) (toSusp X)
Proposition-7 n X cX = isConnectedσ n cX

-- Definition 8 (Fibre Sequences)
Definition-8 : (A B C : Pointed₀) → Type₁
Definition-8 = FiberSeq

-- Long exact sequence of homotopy groups
-- Where (fiberSequence F) is the sequence of groups:
-- ..., π (n + 1) (C), π n A, π n B, π n C, π (n - 1) A, ...
-- and (fiberSequenceEgges F) is the sequence of maps between them,
-- this is a proof that together these form a long exact sequence of groups.
Long-exact-sequence : {A B C : Pointed ℓ} (F : FiberSeq A B C)
                          → isLES (fiberSequence F) (fiberSequenceEdges F)
Long-exact-sequence F = fiberSequenceIsLES F

-- Definition 9 (Cofibre Sequences)
Definition-9 : (A B C : Pointed₀) → Type₁
Definition-9 = CofiberSeq

-- Proposition 10 (if X → Y → Z is a cofibre sequence, then so is Y → Z → Susp X)
Proposition-10 : (A B C : Pointed₀) → CofiberSeq A B C → CofiberSeq B C (S∙ A)
Proposition-10 A B C = copuppe             

-- Corollary 11
-- Susp n X → Susp n Y → Susp n Z is a cofiber sequence
Corollary-11-1 : (A B C : Pointed₀) → CofiberSeq A B C → (n : ℕ) → CofiberSeq (Susp∙^ (suc n) A) (Susp∙^ (suc n) B) (Susp∙^ (suc n) C)
Corollary-11-1 A B C S n = copuppe-Cof (suc n) S
-- Susp n Y → Susp n Z → Susp (1 + n) X is a cofiber sequence
Corollary-11-2 : (A B C : Pointed₀) → CofiberSeq A B C → (n : ℕ) → CofiberSeq (Susp∙^ (suc n) B) (Susp∙^ (suc n) C) (Susp∙^ (suc (suc n)) A)
Corollary-11-2 A B C S n = copuppe-Dom (suc n) S
-- Susp n Z → Susp (1 + n) X → Susp (1 + n) Y is a cofiber sequence
Corollary-11-3 : (A B C : Pointed₀) → CofiberSeq A B C → (n : ℕ) → CofiberSeq (Susp∙^ (suc n) C) (Susp∙^ (suc (suc n)) A) (Susp∙^ (suc (suc n)) B)
Corollary-11-3 A B C S n = copuppe-Ext (suc n) S 

-- Proposition 12 (connectivity of maps between cofibers)
Proposition-12 : (n : ℕ) {A B C A' B' C' : Pointed ℓ}
    (S : CofiberSeq A B C) (S' : CofiberSeq A' B' C')
    (f : (CofiberSeqDom S) →∙ (CofiberSeqDom S'))
    (g : (CofiberSeqExt S) →∙ (CofiberSeqExt S'))
    (p : (g ∘∙ CofiberSeqInc S) ≡ (CofiberSeqInc S' ∘∙ f))
    → isConnectedFun n (fst f)
    → isConnectedFun (1 + n) (fst g)
    → isConnectedFun (1 + n) (fst (CofiberSeqMap S S' f g p))
Proposition-12 = CofiberSeqMapConn

-- Corollary 13 (connectivity of suspension map)
Corollary-13 : (n : ℕ) {A B : Type₀} (f : A → B)
  → isConnectedFun n f
  → isConnectedFun (suc n) (suspFun f)
Corollary-13 n f cf = isConnectedSuspFun f n cf

-- Proposition 14 (connectivity of join map)
Proposition-14 : {ℓ' : Level} {X₁ X₂ : Type ℓ} {Y₁ Y₂ : Type ℓ'}
    (f₁ : X₁ → Y₁) (f₂ : X₂ → Y₂)
    (n₁ n₂ m₁ m₂ : HLevel)
    (k : HLevel) (hk₁ : k ≤ n₁ + m₂) (hk₂ : k ≤ n₂ + m₁)
    → isConnectedFun n₁ f₁ → isConnectedFun n₂ f₂
    → isConnected m₁ X₁ → isConnected m₂ Y₂
    → isConnectedFun k (join→ f₁ f₂)
Proposition-14 = isConnectedFunJoin

-- Proposition 15 (distributivity of suspension and join)
Proposition-15 : ∀ {ℓ} (X₁ X₂ : Pointed ℓ) (M₁ M₂ : ℕ)
  → Susp^ (M₁ + M₂) (join (fst X₁) (fst X₂))
   ≡ join (Susp^ M₁ (typ X₁)) (Susp^ M₂ (typ X₂))
Proposition-15 = joinSuspTrick


