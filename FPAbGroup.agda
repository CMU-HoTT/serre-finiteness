
--**** STOCKHOLM  ****
module FPAbGroup where

open import Everything

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.DirectProduct
open import Cubical.Data.Fin
open import Cubical.Data.Nat

private
  variable
    ℓ : Level

-- finite sets, arbitrary hLevel
postulate
  Fin* : ℕ → Type ℓ

postulate
  ℤMod : ℕ → AbGroup ℓ
  ℤ : AbGroup ℓ

postulate
  ℤMod-finite : (n : ℕ) → fst (ℤMod {ℓ} n) ≃ (Fin* {ℓ} n)

-- finitely presented abelian groups
postulate
  isFP : AbGroup ℓ → Type ℓ
  isFP-prop : {A : AbGroup ℓ} → isProp (isFP A)

postulate
  indFP : (P : AbGroup ℓ → Type ℓ) → (∀ A → isProp (P A))
    → (∀ n → P (ℤMod n)) → (P ℤ)
   → (∀ H K → P H → P K → P (AbDirProd H K))
    → (∀ A → isFP A → (P A))
