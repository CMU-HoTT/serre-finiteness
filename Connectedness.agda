module Connectedness where

open import Everything

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.NatMinusOne
open import Cubical.HITs.Join
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.Homotopy.Connected

open import PointedHITs

private
  variable
    ℓ : Level

-- connectivity facts
isConnectedFunPushout : {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Type ℓ}
  (f₁ : X₀ → X₁) (f₂ : X₀ → X₂) (g₁ : Y₀ → Y₁) (g₂ : Y₀ → Y₂)
  (h₀ : X₀ → Y₀) (h₁ : X₁ → Y₁) (h₂ : X₂ → Y₂)
  (e₁ : h₁ ∘ f₁ ≡ g₁ ∘ h₀) (e₂ : h₂ ∘ f₂ ≡ g₂ ∘ h₀)
  (n : HLevel)
  → isConnectedFun n h₀ → isConnectedFun (1 + n) h₁ → isConnectedFun (1 + n) h₂
  → isConnectedFun (1 + n) (Pushout→ f₁ f₂ g₁ g₂ h₀ h₁ h₂ e₁ e₂)
isConnectedFunPushout = isConnectedPushout→

isConnectedFunS∙ : {X Y : Pointed ℓ} (f : X →∙ Y) (n : HLevel)
  → isConnectedFun n (fst f)
  → isConnectedFun n (fst (S∙→ f))
isConnectedFunS∙ f n con b =
  isConnectedSubtr n 1 (isConnectedSuspFun (fst f) n con b)

postulate
  isConnectedFunJoin : {X₁ Y₁ X₂ Y₂ : Type ℓ} (f₁ : X₁ → Y₁) (f₂ : X₂ → Y₂)
    (n₁ n₂ m₁ m₂ : HLevel)
    (k : HLevel) (hk₁ : n₁ + m₂ ≤ k) (hk₂ : m₁ + n₂ ≤ k)
    → isConnectedFun n₁ f₁ → isConnectedFun n₂ f₂
    → isConnected m₁ Y₁ → isConnected m₂ Y₂
    → isConnectedFun k (join→ f₁ f₂)

  wlp : {A B X Y : Type ℓ} (f : A → B) (g : X → Y) → Type ℓ
  -- wlp f g = ∀ (h : A → X) (k : B → Y) (e : h ∘ g ≡ k ∘ f), ∥ Σ ... ∥₁
  wlp-isProp : {A B X Y : Type ℓ} {f : A → B} {g : X → Y} → isProp (wlp f g)

  liftCell : {X Y : Type ℓ} (f : X → Y) (n : HLevel) (hf : isConnectedFun n f)
    (m : ℕ₋₁) (hm : 1+ m < n) → wlp (λ (_ : Lift (S m)) → lift tt) f
