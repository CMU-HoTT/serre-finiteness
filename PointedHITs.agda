module PointedHITs where

open import Everything

open import Cubical.HITs.Join
open import Cubical.HITs.Susp
open import Cubical.HITs.S1

private
  variable
    ℓ : Level

-- Generalities

--join∙ : Pointed ℓ → Pointed ℓ → Pointed ℓ
--join∙ ( A , a ) ( B , b ) = ( join A B , inl a )

-- Σ and Σ∙ are taken
S∙ : Pointed ℓ → Pointed ℓ
S∙ A = Susp∙ (typ A)

S∙→ : {X Y : Pointed ℓ} → (X →∙ Y) → (S∙ X →∙ S∙ Y)
S∙→ f = suspFun (fst f) , refl

S¹∙ : Pointed _
S¹∙ = ( S¹ , base )
