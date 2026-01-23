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

-- Definition 13 (Connected Covers)
Definition-13 : Pointed₀ → ℕ → Pointed₀
Definition-13 = _<_>

-- Master theorem A (SAF is closed under taking connected covers)
Theorem-A : (X : Pointed ℓ) (safX : saf X) (scX : isConnected 3 (typ X)) (n : ℕ) → saf (X < (suc n) >)
Theorem-A = saf→saf<->

-- Master theorem B (lowest non-trivial homotopy group of a highly connected SAF space is FP)
Theorem-B : (X : Pointed ℓ) (hX : saf X) (n : ℕ) (cX : isConnected (3 + n) (typ X)) → isFP (πAb n X)
Theorem-B = saf→isFPBottomπ

-- Slight difference from the paper
-- Rather than theorem 14, we use the following slightly weaker theorem to derive the finiteness theorem:
-- Simply connected, stably almost finite types have finitely presented homotopy groups 
Theorem-14-var : (X : Pointed ℓ) (safX : saf X) (scX : isConnected 3 (typ X)) (n : ℕ) → isFP (πAb n X)
Theorem-14-var = saf→isFPπ

-- Definition 17 (Finite CW Complexes)
-- Universe polymorphic
Definition-17 : (ℓ : Level) → Type (ℓ-suc ℓ)
Definition-17 = FinCW

-- Example 18 (FinCW is closed under Susp)
Example-18 : (n : ℕ) (C : Type ℓ) → isFinCW C → isFinCW (Susp^ n C)
Example-18 {ℓ} n C = isFinCWSusp {ℓ} {n} C

-- Definition 19 (n-Finite Types)
-- Note that the Agda conventions for finiteness of types and dimensions of CW complexes are off by one from what appears in the paper
-- To translate from Agda indices to paper indices, subtract one.
Definition-19 : HLevel → Type ℓ → Type (ℓ-suc ℓ)
Definition-19 = nFinite-nDim

-- Proposition 20 (transferring finiteness along connected maps)
-- Note also that conventions for connectedness are off by two
-- So here, in the numbering conventions of the paper, our hypotheses are that Y is (n - 1)-finite, and f is (n - 1)-connected
Proposition-20 : {X Y : Type ℓ} (f : X → Y)
                 (n : HLevel) (hf : isConnectedFun (1 + n) f)
                 → nFinite n Y → nFinite n X
Proposition-20 = nFiniteApprox'

-- Propossition 21 (nFinite types are closed under taking cofibers)
Proposition-21 : {n : ℕ} {X Y Z : Pointed ℓ} → CofiberSeq X Y Z
    → nFinite n (typ X)
    → nFinite (1 + n) (typ Y)
    → nFinite (1 + n) (typ Z)
Proposition-21 = cofNFinite

-- Definition 23 (Stably n-Finite Types)
Definition-23 : HLevel → Pointed ℓ → Type (ℓ-suc ℓ)
Definition-23 = stablyNFinite 

-- Propositions 24 and 25 (join is stably k-finite for suitable k)
Proposition-24 : (X Y : Pointed ℓ) (m₁ m₂ n₂ : HLevel)
  (hXm₁ : isConnected (m₁ + 2) (typ X)) (hX₁ : stablyNFinite 1 X)
  (hXm₂ : isConnected m₂ (typ Y)) (hXn₂ : stablyNFinite n₂ Y)
  (k : HLevel) (hk₁ : k ≤ 1 + m₂) (hk₂ : k ≤ n₂ + (m₁ + 2))
  → stablyNFinite k (join∙ X Y)
Proposition-24 {ℓ} X Y = stablyNFiniteJoin-alt {ℓ} {X} {Y}

Proposition-25 : (X Y : Pointed ℓ) (m₁ n₁ m₂ n₂ : HLevel)
  (hmn₁ : m₁ ≤ n₁)
  (hXm₁ : isConnected m₁ (typ X)) (hXn₁ : stablyNFinite n₁ X)
    (hXm₂ : isConnected m₂ (typ Y)) (hXn₂ : stablyNFinite n₂ Y)
  (k : HLevel) (hk₁ : k ≤ n₁ + m₂) (hk₂ : k ≤ n₂ + m₁)
  → stablyNFinite k (join∙ X Y)
Proposition-25 {ℓ} X Y = stablyNFiniteJoin {ℓ} {X} {Y}

-- Definition 26 (Stably Almost Finite Types)
Definition-26 : Pointed ℓ → Type (ℓ-suc ℓ)
Definition-26 = saf

-- Proposition 27 (more closure properties for stably almost finite types)
-- Closure under products
Proposition-27-1 : {X Y : Pointed ℓ} → saf X → saf Y → saf (X ×∙ Y)
Proposition-27-1 {ℓ} {X} {Y} = saf× {ℓ} {X} {Y}
-- Closure under V (wedge product)
Proposition-27-2 : {X Y : Pointed ℓ} → saf X → saf Y → saf (X ⋁∙ₗ Y)
Proposition-27-2 {ℓ} {X} {Y} = saf⋁ {ℓ} {X} {Y} 
-- Closure under /\ (smash product)
Proposition-27-3 : {X Y : Pointed ℓ} → saf X → saf Y → saf (X ⋀∙ Y)
Proposition-27-3 = saf⋀

-- Note that the file SAF.agda contains proofs of many more closure properties for all these concepts, we have only highlighted a few in the paper.

-- Corollary 29 (iterating Ganea)
module _ {X : Pointed ℓ} {Y : Pointed ℓ} (f : X →∙ Y) where
    open Ganea^ f
    -- The ``elbow'' cofibre sequences, for instance
    -- fiber * ...
    --  |
    --  V
    --  E^(n) --> E^(n + 1)
    -- notice we are using the variable E where the paper uses C
    ElbowCofibreSeq : (n : ℕ) → CofiberSeq (join-F n) (E n) (E (1 + n))
    ElbowCofibreSeq = GaneaCofiberSeq

-- Proposition 30 (if B is connected and (Ω B) is SAF, so is B)
-- Remember connectedness conventions are off-by-two
Proposition-30 : {B : Pointed ℓ} (cB : isConnected 2 (typ B)) → saf (Ω B) → saf B
Proposition-30 = safΩ→saf

-- Proposition 31 (if B is simply connected and SAF, then so is (Ω B))
Proposition-31 : {B : Pointed ℓ} (scB : isConnected 3 (typ B)) → saf B → saf (Ω B)
Proposition-31 = saf→safΩ

-- Proposition 32 (if F → E → B is a fibre sequence and B is simply connected, and B and F are SAF, then so is E)
Proposition-32 : {F E B : Pointed ℓ} (S : FiberSeq F E B) (scB : isConnected 3 (typ B)) → saf B → saf F → saf E
Proposition-32 = safTotal

-- Proposition 35 (fiber of the map X<n + 1> → X<n> is an Eilenberg-MacLane space)
-- Indices shifted-by-one
Proposition-35 : (X : Pointed ℓ) (n : ℕ) → FiberSeq (EM∙ (πAb n X) (suc n)) (X < (2 + n) >) (X < (suc n) >)
Proposition-35 = <->EMFibSeq

-- Proposition 36 (if G is FP, then K(G, n) are all SAF)
Proposition-36 : (G : AbGroup ℓ) (fpG : isFP G) (n : ℕ) → saf (EM∙ G (suc n))
Proposition-36 = isFP→safEM'

-- Notice theorem 37 appears in the where clause in proof of saf→isFPBottomπ (Master theorem B)

-- Theorem 41 (The Serre Finiteness Theorem)
-- Note that we introduce some special notation -- πSphere n m -- for the nth homotopy groups of the m-dimensional sphere
Theorem-41 : (n m : ℕ) → isFP (πSphere n m)
Theorem-41 = isFPπSphere

-- Section 4: On the formalisation

-- Proposition 42 (Induction for finitely presentable abelian groups)
Proposition-42 : (P : AbGroup₀ → Type ℓ) → (∀ G → isProp (P G))
   → (∀ n → P (ℤMod n))
   → (∀ H K → P H → P K → P (AbDirProd H K))
   → (∀ G → isFP G → (P G))
Proposition-42 = indFP