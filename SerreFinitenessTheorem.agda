{-# OPTIONS --lossy-unification --safe #-}
module SerreFinitenessTheorem where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma

open import Cubical.Homotopy.Connected
open import Cubical.HITs.Sn hiding (S)

open import SAF
open import FPAbGroup
open import HomotopyGroups
open import ConnectedCovers.Base
open import ConnectedCovers.EMIsFiber
open import CorollariesToHurewicz
open import CorollariesToGanea

private
  variable
    ℓ ℓ' : Level

isFPId : (X : Pointed ℓ) (n : ℕ) → isFP (πAb n (X < (suc n) >)) ≡ isFP (πAb n X)
isFPId X n = λ i → isFP (πConnCovEq X n n ≤-refl i)

mutual
  saf→isFPπ : (X : Pointed ℓ-zero) (safX : saf X) (scX : isConnected 3 (typ X)) (n : ℕ)
    → isFP (πAb n X)
  saf→isFPπ X safX scX zero = saf→isFPBottomπ X safX 0 scX
  saf→isFPπ X safX scX (suc n) =
    transport (isFPId X (suc n)) (saf→isFPBottomπ (X < (2 + n) >) (saf→saf<-> X safX scX (suc n)) (suc n) (ConnCovIsConn X (2 + n)))

  saf→saf<-> : (X : Pointed ℓ-zero) (safX : saf X) (scX : isConnected 3 (typ X)) (n : ℕ)
    → saf (X < (suc n) >)
  saf→saf<-> X safX scX 0 = transport (λ i → saf (1ConnCovEq X scX i)) safX
  saf→saf<-> X safX scX (suc n) =
    safTotal (<->EMFibSeq X n) (Conn→ConnConnCov X 3 (suc n) scX)
      (saf→saf<-> X safX scX n) (isFP→safEM (πAb n X) (saf→isFPπ X safX scX n) n)

isFPπAbSn : (n m : ℕ) → isFP (πAb n (S (2 + m)))
isFPπAbSn n m = saf→isFPπ (S (2 + m)) (saf-Sn (2 + m)) rem2 n
  where
  rem1 : isConnected 3 (S₊ (2 + m))
  rem1 = isConnectedSubtr' m 3 (sphereConnected (suc (suc m)))

  rem2 : isConnected 3 (S (2 + m) .fst)
  rem2 = isConnectedRetractFromIso 3 rUnit*×Iso rem1


open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.HITs.Susp
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.PinSn
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.AbGroup.Instances.Int
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup.FinitePresentation
open import Cubical.Data.Int
open import Cubical.HITs.SetQuotients
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Algebra.Group.QuotientGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup
open import Cubical.Algebra.Group.Instances.Unit

-- TODO: upstream and add for Group as well
AbGroupIso→AbGroupEquiv : {G : AbGroup ℓ} {H : AbGroup ℓ'} → AbGroupIso G H → AbGroupEquiv G H
AbGroupIso→AbGroupEquiv (e , h) = isoToEquiv e , h

open FinitePresentation
open AbGroupStr

-- This could probably be done nicer
finPresTrivialAbGroup : FinitePresentation {ℓ = ℓ} trivialAbGroup
finPresTrivialAbGroup .nGens = 0
finPresTrivialAbGroup .nRels = 0
finPresTrivialAbGroup .rels = (λ x y → pos 0) , record { pres· = λ x y i x₁ → pos 0 ; pres1 = λ i x → pos 0 ; presinv = λ x i x₁ → pos 0 }
finPresTrivialAbGroup .fpiso .fst .Iso.fun = λ x → [ (λ x₁ → pos 0) ]
finPresTrivialAbGroup .fpiso .fst .Iso.inv = λ x → lift tt
finPresTrivialAbGroup .fpiso .fst .Iso.rightInv = elimProp (λ x → is-set (snd (ℤ[Fin 0 ] /Im _) ) _ _) λ a → cong [_] (funExt (λ { () }))
finPresTrivialAbGroup .fpiso .fst .Iso.leftInv (lift tt) = refl
finPresTrivialAbGroup .fpiso .snd = record { pres· = λ x y i →  [ (λ x₁ → pos 0) ] ; pres1 = λ i → [ (λ x → pos 0) ] ; presinv = λ x i → [ (λ x₁ → pos 0) ] }

isFPTrivialAbGroup : isFP {ℓ = ℓ} trivialAbGroup
isFPTrivialAbGroup = ∣ finPresTrivialAbGroup ∣₁

-- π_{n+2}(S⁰) = 0
lemma0 : (n : ℕ) → πAb n (S₊∙ 0) ≡ trivialAbGroup
lemma0 n = AbGroupPath _ _ .fst (AbGroupIso→AbGroupEquiv suff)
  where
  suff : GroupIso (πGr (suc n) (S₊∙ 0)) UnitGroup
  suff = {!!}

-- π_{n+2}(S¹) = 0
lemma1 : (n : ℕ) → πAb n (S₊∙ 1) ≡ trivialAbGroup
lemma1 n = AbGroupPath _ _ .fst (AbGroupIso→AbGroupEquiv suff)
  where
  suff : GroupIso (πGr (suc n) (S₊∙ 1)) UnitGroup
  suff = {!!}

isFPπAbS₊ : (n m : ℕ) → isFP (πAb n (S₊∙ m))
isFPπAbS₊ n 0 = subst isFP (sym (lemma0 n)) isFPTrivialAbGroup
isFPπAbS₊ n 1 = subst isFP (sym (lemma1 n)) isFPTrivialAbGroup
isFPπAbS₊ n (suc (suc m)) = subst (λ A → isFP (πAb n A)) (sym rem) (isFPπAbSn n m)
  where
  rem : S₊∙ (suc (suc m)) ≡ S (suc (suc m))
  rem = ΣPathP ((isoToPath (iso (λ x → (x , tt*)) fst (λ { (x , tt*) → refl }) λ _ → refl))
               , toPathP (λ i → north , tt*))
