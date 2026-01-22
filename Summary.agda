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
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.DirectProduct
open import Cubical.Algebra.AbGroup.Instances.Int
open import Cubical.Algebra.AbGroup.Instances.IntMod renaming (ℤAbGroup/_ to ℤMod)

open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool hiding (_≤_)
open import Cubical.Data.Sigma

open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Freudenthal
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.EilenbergMacLane.Base

open import Cubical.HITs.Sn hiding (S)
open import Cubical.HITs.Pushout
open import Cubical.HITs.Truncation
open import Cubical.HITs.Susp
open import Cubical.HITs.SmashProduct
open import Cubical.HITs.Join
open import Cubical.HITs.Wedge

open import Cubical.CW.Base

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

-- Section 2: Background

-- Definition 5 (Connected Covers)
Definition-5 : Pointed₀ → ℕ → Pointed₀
Definition-5 = _<_>

-- Definition 6 (homotopy groups)
Definition-6 : (n : ℕ) → Pointed₀ → Group₀
Definition-6 n = πGr n

-- Definition 8 (Fibre Sequences)
Definition-8 : (X Y Z : Pointed₀) → Type₁
Definition-8 = FiberSeq

-- Long exact sequence of homotopy groups
-- Where (fiberSequence F) is the sequence of groups:
-- ..., π (n + 1) (Z), π n X, π n Y, π n Z, π (n - 1) X, ...
-- and (fiberSequenceEgges F) is the sequence of maps between them,
-- this is a proof that together these form a long exact sequence of groups.
Long-exact-sequence : {X Y Z : Pointed ℓ} (F : FiberSeq X Y Z) → isLES (fiberSequence F) (fiberSequenceEdges F)
Long-exact-sequence F = fiberSequenceIsLES F

-- Definition 9 (Cofibre Sequences)
Definition-9 : (X Y Z : Pointed₀) → Type₁
Definition-9 = CofiberSeq

-- Proposition 10 (if X → Y → Z is a cofibre sequence, then so is Y → Z → Susp X)
Proposition-10 : (X Y Z : Pointed₀) → CofiberSeq X Y Z → CofiberSeq Y Z (S∙ X)
Proposition-10 X Y Z = copuppe             

-- Corollary 11
-- Susp n X → Susp n Y → Susp n Z is a cofiber sequence
Corollary-11-1 : (X Y Z : Pointed₀) → CofiberSeq X Y Z → (n : ℕ) → CofiberSeq (Susp∙^ (suc n) X) (Susp∙^ (suc n) Y) (Susp∙^ (suc n) Z)
Corollary-11-1 X Y Z S n = copuppe-Cof (suc n) S
-- Susp n Y → Susp n Z → Susp (1 + n) X is a cofiber sequence
Corollary-11-2 : (X Y Z : Pointed₀) → CofiberSeq X Y Z → (n : ℕ) → CofiberSeq (Susp∙^ (suc n) Y) (Susp∙^ (suc n) Z) (Susp∙^ (suc (suc n)) X)
Corollary-11-2 X Y Z S n = copuppe-Dom (suc n) S
-- Susp n Z → Susp (1 + n) X → Susp (1 + n) Y is a cofiber sequence
Corollary-11-3 : (X Y Z : Pointed₀) → CofiberSeq X Y Z → (n : ℕ) → CofiberSeq (Susp∙^ (suc n) Z) (Susp∙^ (suc (suc n)) X) (Susp∙^ (suc (suc n)) Y)
Corollary-11-3 X Y Z S n = copuppe-Ext (suc n) S 

-- Proposition 12 (connectivity of maps between cofibers)
Proposition-12 : (n : ℕ) {X Y Z X' Y' Z' : Pointed ℓ}
    (S : CofiberSeq X Y Z) (S' : CofiberSeq X' Y' Z')
    (f : X →∙ X') (g : Y →∙ Y')
    (p : (g ∘∙ CofiberSeqInc S) ≡ (CofiberSeqInc S' ∘∙ f))
    → isConnectedFun n (fst f)
    → isConnectedFun (1 + n) (fst g)
    → isConnectedFun (1 + n) (fst (CofiberSeqMap S S' f g p))
Proposition-12 = CofiberSeqMapConn

-- Corollary 13 (connectivity of suspension map)
Corollary-13 : (n : ℕ) {X Y : Type₀} (f : X → Y)
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
Proposition-15 : ∀ {ℓ} (X Y : Pointed ℓ) (M₁ M₂ : ℕ)
  → Susp^ (M₁ + M₂) (join (fst X) (fst Y))
   ≡ join (Susp^ M₁ (typ X)) (Susp^ M₂ (typ Y))
Proposition-15 = joinSuspTrick

-- Section 3: A rough outline of the formalised proof

-- Master theorem A (SAF is closed under taking connected covers)
Theorem-A : (X : Pointed ℓ) (safX : saf X) (scX : isConnected 3 (typ X)) (n : ℕ) → saf (X < (suc n) >)
Theorem-A = saf→saf<->

-- Master theorem B (lowest non-trivial homotopy group of a highly connected SAF space is FP)
Theorem-B : (X : Pointed ℓ) (hX : saf X) (n : ℕ) (cX : isConnected (3 + n) (typ X)) → isFP (πAb n X)
Theorem-B = saf→isFPBottomπ

-- Slight difference from the paper
-- Rather than theorem 16, we use the following slightly weaker theorem to derive the finiteness theorem:
-- Simply connected, stably almost finite types have finitely presented homotopy groups 
Theorem-16-var : (X : Pointed ℓ) (safX : saf X) (scX : isConnected 3 (typ X)) (n : ℕ) → isFP (πAb n X)
Theorem-16-var = saf→isFPπ

-- Definition 19 (Finite CW Complexes)
-- Universe polymorphic
Definition-19 : (ℓ : Level) → Type (ℓ-suc ℓ)
Definition-19 = FinCW

-- Example 20 (FinCW is closed under Susp)
Example-20 : (n : ℕ) (C : Type ℓ) → isFinCW C → isFinCW (Susp^ n C)
Example-20 {ℓ} n C = isFinCWSusp {ℓ} {n} C

-- Definition 21 (n-Finite Types)
-- Note that the Agda conventions for finiteness of types and dimensions of CW complexes are off by one from what appears in the paper
-- To translate from Agda indices to paper indices, subtract one.
Definition-21 : HLevel → Type ℓ → Type (ℓ-suc ℓ)
Definition-21 = nFinite-nDim

-- Proposition 22 (transferring finiteness along connected maps)
-- Note also that conventions for connectedness are off by two
-- So here, in the numbering conventions of the paper, our hypotheses are that Y is (n - 1)-finite, and f is (n - 1)-connected
Proposition-22 : {X Y : Type ℓ} (f : X → Y)
                 (n : HLevel) (hf : isConnectedFun (1 + n) f)
                 → nFinite n Y → nFinite n X
Proposition-22 = nFiniteApprox'

-- Propossition 23 (nFinite types are closed under taking cofibers)
Proposition-23 : {n : ℕ} {X Y Z : Pointed ℓ} → CofiberSeq X Y Z
    → nFinite n (typ X)
    → nFinite (1 + n) (typ Y)
    → nFinite (1 + n) (typ Z)
Proposition-23 = cofNFinite

-- Definition 25 (Stably n-Finite Types)
Definition-25 : HLevel → Pointed ℓ → Type (ℓ-suc ℓ)
Definition-25 = stablyNFinite 

-- Propositions 27 and 28 (join is stably k-finite for suitable k)
Proposition-27 : (X Y : Pointed ℓ) (m₁ m₂ n₂ : HLevel)
  (hXm₁ : isConnected (m₁ + 2) (typ X)) (hX₁ : stablyNFinite 1 X)
  (hXm₂ : isConnected m₂ (typ Y)) (hXn₂ : stablyNFinite n₂ Y)
  (k : HLevel) (hk₁ : k ≤ 1 + m₂) (hk₂ : k ≤ n₂ + (m₁ + 2))
  → stablyNFinite k (join∙ X Y)
Proposition-27 {ℓ} X Y = stablyNFiniteJoin-alt {ℓ} {X} {Y}

Proposition-28 : (X Y : Pointed ℓ) (m₁ n₁ m₂ n₂ : HLevel)
  (hmn₁ : m₁ ≤ n₁)
  (hXm₁ : isConnected m₁ (typ X)) (hXn₁ : stablyNFinite n₁ X)
    (hXm₂ : isConnected m₂ (typ Y)) (hXn₂ : stablyNFinite n₂ Y)
  (k : HLevel) (hk₁ : k ≤ n₁ + m₂) (hk₂ : k ≤ n₂ + m₁)
  → stablyNFinite k (join∙ X Y)
Proposition-28 {ℓ} X Y = stablyNFiniteJoin {ℓ} {X} {Y}

-- Definition 29 (Stably Almost Finite Types)
Definition-29 : Pointed ℓ → Type (ℓ-suc ℓ)
Definition-29 = saf

-- Proposition 30 (more closure properties for stably almost finite types)
-- Closure under products
Proposition-30-1 : {X Y : Pointed ℓ} → saf X → saf Y → saf (X ×∙ Y)
Proposition-30-1 {ℓ} {X} {Y} = saf× {ℓ} {X} {Y}
-- Closure under V (wedge product)
Proposition-30-2 : {X Y : Pointed ℓ} → saf X → saf Y → saf (X ⋁∙ₗ Y)
Proposition-30-2 {ℓ} {X} {Y} = saf⋁ {ℓ} {X} {Y} 
-- Closure under /\ (smash product)
Proposition-30-3 : {X Y : Pointed ℓ} → saf X → saf Y → saf (X ⋀∙ Y)
Proposition-30-3 = saf⋀

-- Note that the file SAF.agda contains proofs of many more closure properties for all these concepts, we have only highlighted a few in the paper.

-- Corollary 32 (iterating Ganea)
module _ {X : Pointed ℓ} {Y : Pointed ℓ} (f : X →∙ Y) where
    open Ganea^ f
    -- The ``elbow'' cofibre sequences, for instance
    -- fiber * ...
    --  |
    --  V
    --  E(n) --> E(n + 1)
    ElbowCofibreSeq : (n : ℕ) → CofiberSeq (join-F n) (E n) (E (1 + n))
    ElbowCofibreSeq = GaneaCofiberSeq

-- Proposition 33 (if X is connected and (Ω X) is SAF, so is X)
-- Remember connectedness conventions are off-by-two
Proposition-33 : {X : Pointed ℓ} (cX : isConnected 2 (typ X)) → saf (Ω X) → saf X
Proposition-33 = safΩ→saf

-- Proposition 34 (if X is simply connected and SAF, then so is (Ω X))
Proposition-34 : {X : Pointed ℓ} (scX : isConnected 3 (typ X)) → saf X → saf (Ω X)
Proposition-34 = saf→safΩ

-- Proposition 35 (if X → Y → Z is a fibre sequence and Z is simply connected, and Z and X are SAF, then so is Y)
Proposition-35 : {X Y Z : Pointed ℓ} (S : FiberSeq X Y Z) (scZ : isConnected 3 (typ Z)) → saf Z → saf X → saf Y
Proposition-35 = safTotal

-- Proposition 38 (fiber of the map X<n + 1> → X<n> is an Eilenberg-MacLane space)
-- Indices shifted-by-one
Proposition-38 : (X : Pointed ℓ) (n : ℕ) → FiberSeq (EM∙ (πAb n X) (suc n)) (X < (2 + n) >) (X < (suc n) >)
Proposition-38 = <->EMFibSeq

-- Proposition 39 (if G is FP, then K(G, n) are all SAF)
Proposition-39 : (G : AbGroup ℓ) (fpG : isFP G) (n : ℕ) → saf (EM∙ G (suc n))
Proposition-39 = isFP→safEM'

-- Notice theorem 40 appears in the where clause in proof of saf→isFPBottomπ (Master theorem B)

-- Theorem 44 (The Serre Finiteness Theorem)
-- Note that we introduce some special notation -- πSphere n m -- for the nth homotopy groups of the m-dimensional sphere
Theorem-44 : (n m : ℕ) → isFP (πSphere n m)
Theorem-44 = isFPπSphere

-- Section 4: On the formalisation

-- Proposition 45 (Induction for finitely presentable abelian groups)
Proposition-45 : (P : AbGroup₀ → Type ℓ) → (∀ G → isProp (P G))
   → (∀ n → P (ℤMod n))
   → (∀ H K → P H → P K → P (AbDirProd H K))
   → (∀ G → isFP G → (P G))
Proposition-45 = indFP