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

-- functoriality of join
joinFunctExt : {X₀ X₁ Y₀ Y₁ Z₀ Z₁ : Type ℓ} (f₀ : X₀ → Y₀) (f₁ : X₁ → Y₁)
              (g₀ : Y₀ → Z₀) (g₁ : Y₁ → Z₁) (x : join X₀ X₁)
           → (join→ (g₀ ∘ f₀) (g₁ ∘ f₁)) x
            ≡ ((join→ g₀ g₁) ∘ (join→ f₀ f₁)) x
joinFunctExt f₀ f₁ g₀ g₁ (inl x) = refl
joinFunctExt f₀ f₁ g₀ g₁ (inr x) = refl
joinFunctExt f₀ f₁ g₀ g₁ (push a b i) = refl

-- commutativity of join→
join→-commExt : {W X Y Z : Type ℓ} (f : W → Y) (g : X → Z) (x : join X W)
  → (join-commFun ∘ (join→ f g) ∘ join-commFun) x ≡ (join→ g f) x
join→-commExt f g (inl x) = refl
join→-commExt f g (inr x) = refl
join→-commExt f g (push a b i) = refl

join→-comm : {W X Y Z : Type ℓ} (f : W → Y) (g : X → Z)
  → join-commFun ∘ (join→ f g) ∘ join-commFun ≡ (join→ g f)
join→-comm f g = funExt (join→-commExt f g)

joinFunct : {X₀ X₁ Y₀ Y₁ Z₀ Z₁ : Type ℓ} (f₀ : X₀ → Y₀) (f₁ : X₁ → Y₁)
              (g₀ : Y₀ → Z₀) (g₁ : Y₁ → Z₁)
           → (join→ (g₀ ∘ f₀) (g₁ ∘ f₁))
            ≡ (join→ g₀ g₁) ∘ (join→ f₀ f₁)
joinFunct f₀ f₁ g₀ g₁ = funExt (joinFunctExt f₀ f₁ g₀ g₁)

-- connectivity facts
connectedMin : (n₁ n₂ : ℕ) {X Y Z : Type ℓ} (f : X → Y) (g : Y → Z)
            → isConnectedFun n₁ f → isConnectedFun n₂ g
            → (k : ℕ) → k ≤ n₁ → k ≤ n₂
            → isConnectedFun k (g ∘ f)
connectedMin n₁ n₂ f g hf hg k (m₁ , p₁) (m₂ , p₂) =
  isConnectedComp g f k
    (isConnectedFunSubtr k m₂ g
       (transport (λ i → isConnectedFun (p₂ (~ i)) g) hg))
    (isConnectedFunSubtr k m₁ f
       (transport (λ i → isConnectedFun (p₁ (~ i)) f) hf))

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

joinConnected' : (m n : ℕ) → {A A' : Type ℓ} (B : Type ℓ) (v : A → A')
               → isConnectedFun m v
               → isConnected n B
               → isConnectedFun (m + n) (join→ (idfun B) v)
joinConnected' m n B v hv hB =
  transport (λ i → isConnectedFun (m + n) (join→-comm v (idfun B) i))
            (isConnectedComp (join-commFun ∘ (join→ v (idfun B)))
                             join-commFun
                             (m + n)
                             (isConnectedComp
                                join-commFun
                                (join→ v (idfun B))
                                (m + n)
                                (isEquiv→isConnected join-commFun
                                   (isIsoToIsEquiv (IsoToIsIso join-comm))
                                   (m + n))
                                (joinConnected m n hv hB))
                             (isEquiv→isConnected join-commFun
                                (isIsoToIsEquiv (IsoToIsIso join-comm))
                                (m + n)))

isConnectedFunJoin : {X₁ Y₁ X₂ Y₂ : Type ℓ} (f₁ : X₁ → Y₁) (f₂ : X₂ → Y₂)
    (n₁ n₂ m₁ m₂ : HLevel)
    (k : HLevel) (hk₁ : k ≤ n₁ + m₂) (hk₂ : k ≤ n₂ + m₁)
    → isConnectedFun n₁ f₁ → isConnectedFun n₂ f₂
    → isConnected m₁ X₁ → isConnected m₂ Y₂
    → isConnectedFun k (join→ f₁ f₂)
isConnectedFunJoin f₁ f₂ n₁ n₂ m₁ m₂ k hk₁ hk₂ hf₁ hf₂ hX₁ hY₂ =
  transport (λ i → isConnectedFun k
                    (joinFunct (idfun _) f₂ f₁ (idfun _) (~ i)))
            (connectedMin (n₂ + m₁) (n₁ + m₂)
              (join→ (idfun _) f₂) (join→ f₁ (idfun _))
              (joinConnected' n₂ m₁ _ _ hf₂ hX₁)
              (joinConnected n₁ m₂ hf₁ hY₂)
              k hk₂ hk₁)

postulate
  wlp : {A B X Y : Type ℓ} (f : A → B) (g : X → Y) → Type ℓ
  -- wlp f g = ∀ (h : A → X) (k : B → Y) (e : h ∘ g ≡ k ∘ f), ∥ Σ ... ∥₁
  wlp-isProp : {A B X Y : Type ℓ} {f : A → B} {g : X → Y} → isProp (wlp f g)

  liftCell : {X Y : Type ℓ} (f : X → Y) (n : HLevel) (hf : isConnectedFun n f)
    (m : ℕ₋₁) (hm : 1+ m < n) → wlp (λ (_ : Lift (S m)) → lift tt) f
