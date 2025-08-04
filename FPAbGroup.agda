{-# OPTIONS --lossy-unification #-}
--**** STOCKHOLM  ****
module FPAbGroup where

open import Everything

open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.DirectProduct
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup
open import Cubical.Algebra.AbGroup.Instances.Int
open import Cubical.Algebra.AbGroup.Instances.IntMod renaming (ℤAbGroup/_ to ℤMod)
open import Cubical.Algebra.AbGroup.FinitePresentation
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Data.Fin.Inductive
open import Cubical.Data.Int using (+Comm)
open import Cubical.Data.Nat
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Algebra.Group.QuotientGroup
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.AbGroup.Instances.IntMod
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Data.List
open import Cubical.Data.Fin as FinAlt using (isContrFin1)
open import Cubical.Data.Int
open import Cubical.HITs.PropositionalTruncation as PT

open import LastMinuteLemmas.Smith

open FinitePresentation

private
  variable
    ℓ : Level

AbGroup₀ = AbGroup ℓ-zero

ℤMod-finite : (n : ℕ) → fst (ℤMod (suc n)) ≃ (Fin (suc n))
ℤMod-finite n = isoToEquiv (Iso-Fin-InductiveFin (suc n))

-- finitely presented abelian groups
isFP : AbGroup ℓ → Type ℓ
isFP A = ∥ FinitePresentation A ∥₁

isFP-prop : {A : AbGroup ℓ} → isProp (isFP A)
isFP-prop = squash₁

indFP : (P : AbGroup₀ → Type ℓ) → (∀ A → isProp (P A))
   → (∀ n → P (ℤMod n))
   → (∀ H K → P H → P K → P (AbDirProd H K))
   → (∀ A → isFP A → (P A))
indFP P pr bas prod A = PT.rec (pr A)
  λ FP → subst P (AbGroupPath _ _ .fst
          (GroupIso→GroupEquiv
            (invGroupIso (isFP→isFPGroupNormalForm FP .snd .snd))))
              (main _ _)
 where
 lem : AbGroupEquiv (ℤAbGroup/ 1) (trivialAbGroup {ℓ-zero})
 fst lem = isContr→Equiv FinAlt.isContrFin1 (tt* , (λ {tt* → refl}))
 snd lem = makeIsGroupHom λ _ _ → refl

 main : (l : List ℤ) (n : ℕ) → P (FPGroupNormalForm' (pos n) l)
 main [] zero = subst P (AbGroupPath _ _ .fst lem) (bas 1)
 main [] (suc n) = prod _ _ (bas 0) (main [] n)
 main (x ∷ l) n = prod _ _ (bas (abs x)) (main l n)
