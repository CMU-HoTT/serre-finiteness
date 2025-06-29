
--**** STOCKHOLM ****
module FiniteCW where

open import Everything

open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.HITs.Join
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Homotopy.Connected
open import Cubical.CW.Base renaming (isFinCW to isFinCW')

--open import FiberOrCofiberSequences.CofiberBase

private
  variable
    ℓ : Level

-- possibly this exists elsewhere
Susp^ : ℕ → Type ℓ → Type ℓ
Susp^ 0 X = X
Susp^ (suc n) X = Susp^ n (Susp X)

postulate
  arithmetricky : (n m : ℕ) → suc (n + m) ≡ n + (suc m)

Susp^-conn : (m n : ℕ) (X : Type ℓ) → isConnected m X
             → isConnected (n + m) (Susp^ n X)
Susp^-conn m zero X hX = hX
Susp^-conn m (suc n) X hX =
  transport (λ i → isConnected (arithmetricky n m (~ i)) (Susp^ (suc n) X))
             (Susp^-conn (suc m) n (Susp X) (isConnectedSusp m hX))

  -- The type of "finite CW complex structures".
  -- We need to expose this separately from `isFinCW`
  -- if we want to define e.g. `nFinite n X` as a *small* proposition.
  -- (Possibly we don't really care.)
FinCW : (ℓ : Level) → Type (ℓ-suc ℓ)
FinCW = finCW

decodeFinCW : finCW ℓ → Type ℓ
decodeFinCW = fst

isFinCW : Type ℓ → Type (ℓ-suc ℓ)
isFinCW A = ∥ isFinCW' A ∥₁

isFinCW-isProp : {X : Type ℓ} → isProp (isFinCW X)
isFinCW-isProp = squash₁

-- postulate
isFinCW-def : {X : Type ℓ} → isFinCW X ≃ (∥ (Σ[ C ∈ FinCW ℓ ] (X ≡ decodeFinCW C)) ∥₁)
isFinCW-def {ℓ = ℓ} {X = X} = propBiimpl→Equiv squash₁ squash₁
  (PT.map (λ A → (X , ∣ A ∣₁) , refl))
  (PT.rec squash₁ (uncurry (uncurry λ X' A p → help X' A X (sym p))))
  where
  help : (x : Type ℓ) (y : ∥ isFinCW' x ∥₁)
      (X : Type ℓ)
      (y₁ : decodeFinCW (x , y) ≡ X) →
      ∥ isFinCW' X ∥₁
  help X A = J> A

isFinCW-def-fun : {X : Type ℓ} → isFinCW X → (∥ (Σ[ C ∈ FinCW ℓ ] X ≡ decodeFinCW C) ∥₁)
isFinCW-def-fun = fst isFinCW-def

  -- `isNDimFinCW n X` = "X is a finite (n-1)-dimensional CW complex".
hasNDimFinCW : ℕ → Type ℓ → Type (ℓ-suc ℓ)
hasNDimFinCW {ℓ = ℓ} n X = Σ[ X' ∈ finCWskel ℓ n ] X ≃ realise (finCWskel→CWskel n X')

isNDimFinCW : ℕ → Type ℓ → Type (ℓ-suc ℓ)
isNDimFinCW n X = ∥ hasNDimFinCW n X ∥₁

isNDimFinCW-isProp : {n : ℕ} {X : Type ℓ} → isProp (isNDimFinCW n X)
isNDimFinCW-isProp = squash₁

postulate
  -- closure under pushouts, products, etc.

  isNDimFinCW→isFinCW : {n : ℕ} {X : Type ℓ} → isNDimFinCW n X
                                              → isFinCW X

  isFinCWUnit : isFinCW (Unit* {ℓ = ℓ})

  isFinCWSn : {n : ℕ} → isFinCW (S₊ n)

  isFinCWSusp : {n : ℕ} (X : Type ℓ) → isFinCW (Susp^ n X)

  isFinCWPushout : {X Y Z : Type ℓ} (f : X → Y) (g : X → Z)
    → isFinCW X → isFinCW Y → isFinCW Z → isFinCW (Pushout f g)

  isFinCWJoin : {X Y : Type ℓ} → isFinCW X → isFinCW Y → isFinCW (join X Y)

-- "Obstruction theory".
  liftFromNDimFinCW : (n : ℕ) (X : Type ℓ) (hX : isNDimFinCW n X)
    {Y Z : Type ℓ} (f : Y → Z) (hf : isConnectedFun (2 + n) f) (g : X → Z)
    → ∃[ l ∈ (X → Y) ] (f ∘ l ≡ g)

  mapFromNSkel : (X : Type ℓ) (hX : isFinCW X) (n : ℕ)
    → ∃[ Y ∈ Type ℓ ] Σ[ hY ∈ isNDimFinCW n Y ] Σ[ f ∈ (Y → X) ] isConnectedFun (1 + n) f
