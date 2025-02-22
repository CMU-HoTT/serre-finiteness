
--**** STOCKHOLM  ****
module FPAbGroup where

open import Everything

open import Cubical.Algebra.AbGroup
open import Cubical.Data.Nat

private
  variable
    ℓ : Level

postulate
  ℤMod : ℕ → AbGroup ℓ

  ℤ^ : ℕ → AbGroup ℓ

-- finitely presented abelian groups
postulate
  isFP : AbGroup ℓ → Type ℓ
  isFP-prop : {A : AbGroup ℓ} → isProp (isFP A)

postulate
  indFP : (P : AbGroup ℓ → Type ℓ) → (∀ A → isProp (P A))
    → (∀ n → P (ℤMod n)) → (∀ n → P (ℤ^ n))
    → (∀ A → isFP A → (P A))
