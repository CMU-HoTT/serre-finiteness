
--**** STOCKHOLM ****
module FiniteCW where

open import Everything

open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.HITs.Join
open import Cubical.HITs.Truncation
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.Homotopy.Connected

private
  variable
    ℓ : Level

-- possibly this exists elsewhere
Susp^ : ℕ → Type ℓ → Type ℓ
Susp^ 0 X = X
Susp^ (suc n) X = Susp^ n (Susp X)

-- finite CW complexes
postulate
  -- The type of "finite CW complex structures".
  -- We need to expose this separately from `isFinCW`
  -- if we want to define e.g. `nFinite n X` as a *small* proposition.
  -- (Possibly we don't really care.)
  FinCW : (ℓ : Level) → Type ℓ
  decodeFinCW : FinCW ℓ → Type ℓ

  isFinCW : Type ℓ → Type ℓ
  isFinCW-isProp : {X : Type ℓ} → isProp (isFinCW X)

  isFinCW-def : {X : Type ℓ} → isFinCW X ≃ (∥ (Σ[ C ∈ FinCW ℓ ] (X ≡ decodeFinCW C)) ∥ 1)

  isFinCW-def-fun : {X : Type ℓ} → isFinCW X → (∥ (Σ[ C ∈ FinCW ℓ ] X ≡ decodeFinCW C) ∥ 1)

  -- closure under pushouts, products, etc.

  isFinCWUnit : isFinCW (Unit* {ℓ = ℓ})

  isFinCWSn : {n : ℕ} → isFinCW (S₊ n)

  isFinCWSusp : {n : ℕ} (X : Type ℓ) → isFinCW (Susp^ n X)

  isFinCWPushout : {X Y Z : Type ℓ} (f : X → Y) (g : X → Z)
    → isFinCW X → isFinCW Y → isFinCW Z → isFinCW (Pushout f g)

  isFinCWJoin : {X Y : Type ℓ} → isFinCW X → isFinCW Y → isFinCW (join X Y)

  -- Suggestion on the use of `HLevel`s:
  -- following the lead of `πGr`, `isConnected`, etc.,
  -- use `0 : HLevel` for the smallest meaningful value.
  -- In this case, the smallest meaningful value is -1 and so
  -- `isNDimFinCW n X` = "X is a finite (n-1)-dimensional CW complex".

  isNDimFinCW : HLevel → Type ℓ → Type ℓ
  isNDimFinCW-isProp : {n : HLevel} {X : Type ℓ} → isProp (isNDimFinCW n X)

  -- "Obstruction theory".
  liftFromNDimFinCW : (n : HLevel) (X : Type ℓ) (hX : isNDimFinCW n X)
    {Y Z : Type ℓ} (f : Y → Z) (hf : isConnectedFun (2 + n) f) (g : X → Z)
    → ∥ Σ[ l ∈ (X → Y) ] f ∘ l ≡ g ∥ 1

  mapFromNSkel : (X : Type ℓ) (hX : isFinCW X) (n : HLevel)
    → ∥ Σ[ Y ∈ Type ℓ ] Σ[ hY ∈ isNDimFinCW n Y ] Σ[ f ∈ (Y → X) ] isConnectedFun n f ∥ 1
