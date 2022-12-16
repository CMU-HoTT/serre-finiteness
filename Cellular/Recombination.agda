module Cellular.Recombination where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sum
open import Cubical.HITs.Pushout

open import Cellular.RelativeCellComplex
open import Pushout.Coproduct
open import Pushout.IsPushout

private
  variable
    ℓi ℓ ℓ' : Level

module Recombination {A A' B B' : Type ℓ} (j : A → A') (k : B → B')
  {X X' Y Y' : Type ℓ} (f : X → X') (g : X' → Y) (h : Y → Y')
  (hf : isPushoutOf j f) (hh : isPushoutOf k h) (l : B → X) (p : g ∘ f ∘ l ≡ hh .fst) where
  X'' : Type ℓ
  X'' = Pushout (f ∘ l) k

  f' : X → X''
  f' x = inl (f x)

  s =
    cancel-isPushoutAlong'' {g₁ = g}
      (PushoutIsPushout (f ∘ l) k)
      (paste'IsPushout
        (equivIsPushout {α = p} (idIsEquiv _) (idIsEquiv _))
        (transposeIsPushout (hh .snd .snd .snd)))

  g' : X'' → Y'
  g' = s .fst

  hf'0 : isPushoutOf _ f'
  hf'0 = ipoOfPO
    (pasteIsPushout
      (glue₁IsPushout (hf .snd .snd .snd) l)
      (glue₂IsPushout (transposeIsPushout (PushoutIsPushout (f ∘ l) k)) (hf .snd .fst)))

  hf' : isPushoutOf (map-⊎ j k) f'
  hf' = subst (λ F → isPushoutOf F f') (funExt (elim (λ _ → refl) (λ _ → refl))) hf'0

  hg' : isPushoutOf g g'
  hg' = _ , _ , _ , s .snd .snd .snd

  q : h ∘ g ∘ f ≡ g' ∘ f'
  q = cong (_∘ f) (s .snd .snd .fst)
