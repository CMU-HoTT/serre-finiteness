module Pushout.More where

open import Cubical.Foundations.Everything
open import Cubical.HITs.Pushout

-- Assorted facts about `Pushout`
-- not present in the cubical library.

private
  variable
    ℓ : Level

open Iso

Pushout-id-Iso : {X Y : Type ℓ} (f : X → Y) → Iso (Pushout f (idfun X)) Y
fun (Pushout-id-Iso f) (inl y) = y
fun (Pushout-id-Iso f) (inr x) = f x
fun (Pushout-id-Iso f) (push x i) = f x
inv (Pushout-id-Iso f) y = inl y
rightInv (Pushout-id-Iso f) y = refl
leftInv (Pushout-id-Iso f) (inl y) = refl
leftInv (Pushout-id-Iso f) (inr x) = push x
leftInv (Pushout-id-Iso f) (push x i) j = push x (i ∧ j)

Pushout-id-≃ : {X Y : Type ℓ} (f : X → Y) → Pushout f (idfun X) ≃ Y
Pushout-id-≃ f = isoToEquiv (Pushout-id-Iso f)

