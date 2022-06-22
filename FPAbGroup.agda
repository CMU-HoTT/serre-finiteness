module FPAbGroup where

open import Cubical.Foundations.Everything

open import Cubical.Algebra.AbGroup

private
  variable
    ℓ : Level

-- finitely presented abelian groups
postulate
  isFP : AbGroup ℓ → Type ℓ
  isFP-prop : {A : AbGroup ℓ} → isProp (isFP A)
