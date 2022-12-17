module Pushout.Coproduct where

open import Cubical.Data.Empty as Empty using (⊥*)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Foundations.Everything

open import Pushout.IsPushout

private
  variable
    ℓ ℓ' ℓ'' : Level

Π⊥≡ : {A : Type ℓ'} {f g : ⊥* {ℓ = ℓ} → A} → f ≡ g
Π⊥≡ = funExt λ ()

map⊎≡ : {A B A' B' : Type ℓ} (f : A → B) (g : A' → B')
  → map f g ≡ map (idfun B) g ∘ map f (idfun A')
map⊎≡ f g = funExt (λ { (inl _) → refl ; (inr _) → refl })

module _ {X Y : Type ℓ} {zX : ⊥* → X} {zY : ⊥* → Y} where
  SumIsPushout : {α : _} → isPushout zX zY inl inr α
  SumIsPushout {α} .isPushout.comparisonIsEquiv E =
    cancelEquivL (equivIsEquiv e₂) (equivIsEquiv e₁)
    where
      open Iso
      e₁ : ((X ⊎ Y) → E) ≃ ((X → E) × (Y → E))
      e₁ = Π⊎≃

      e₂ : (Σ[ g' ∈ (X → E) ] Σ[ f' ∈ (Y → E) ] g' ∘ zX ≡ f' ∘ zY)
           ≃ ((X → E) × (Y → E))
      e₂ = Σ-cong-equiv-snd λ _ → Σ-contractSnd λ _ →
           isProp→isContrPath (λ f g → funExt λ ()) _ _

-- Sensible defaults.
SumIsPushout0 : {X Y : Type ℓ} → isPushout {B = X} {C = Y} Empty.rec* Empty.rec* inl inr Π⊥≡
SumIsPushout0 = SumIsPushout

module _ {X X' Y : Type ℓ} {f : X → X'} where
  Sum→₁IsPushout : isPushout f inl inl (map f (idfun Y)) refl
  Sum→₁IsPushout = cancelIsPushout SumIsPushout0 SumIsPushout

module _ {X Y Y' : Type ℓ} {f : Y → Y'} where
  Sum→₂IsPushout : isPushout f inr inr (map (idfun X) f) refl
  Sum→₂IsPushout =
    cancelIsPushout
      (transposeIsPushout SumIsPushout0)
      (transposeIsPushout {α = sym _} SumIsPushout)

{-

     f
   A → B         X ⊔ A → X ⊔ B
 g ↓   ↓ g'  ~~>   ↓       ↓     given a map k : X → C, & same for - ⊔ X.
   C → P           C   →   P
     f'
-}

module _ {A B C P : Type ℓ} {f : A → B} {g : A → C} {g' : B → P} {f' : C → P}
  {α : g' ∘ f ≡ f' ∘ g} (po : isPushout f g g' f' α) {X : Type ℓ} (k : X → C) where
  glue₁IsPushout : isPushout (map f (idfun X)) (rec g k) (rec g' (f' ∘ k)) f' (funExt (elim (λ a → α ≡$ a) (λ _ → refl)))
  glue₁IsPushout = cancel'IsPushout' _ Sum→₁IsPushout po (lUnit _)

  glue₂IsPushout : isPushout (map (idfun X) f) (rec k g) (rec (f' ∘ k) g') f' (funExt (elim (λ _ → refl) (λ a → α ≡$ a)))
  glue₂IsPushout = cancel'IsPushout' _ Sum→₂IsPushout po (lUnit _)
