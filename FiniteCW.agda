module FiniteCW where

open import Cubical.Foundations.Everything

open import Cubical.Data.Fin
open import Cubical.Data.Nat
open import Cubical.Data.NatMinusOne
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.Join
open import Cubical.Homotopy.Connected

open import FPAbGroup
open import HomotopyGroups

private
  variable
    ℓ : Level

abstract
  record AttachedSkeleton n (Skel : Type₀) (Real : Skel → Type₀) : Type₀ where
    field
      skel : Skel
      numCells : ℕ
      attaching : Fin numCells → S (ℕ→ℕ₋₁ n) → Real skel

  IndexedFinCW : ℕ → Type₀
  decodeIndexedFinCW : {n : ℕ} → IndexedFinCW n → Type₀

  IndexedFinCW 0 = ℕ
  IndexedFinCW (suc n) = AttachedSkeleton n (IndexedFinCW n) decodeIndexedFinCW

  decodeIndexedFinCW {n = 0} cells = Fin cells
  decodeIndexedFinCW {n = suc n} skel = Pushout (uncurry (skel .AttachedSkeleton.attaching)) fst

  -- The type of "finite CW complex structures".
  -- We need to expose this separately from `isFinCW`
  -- if we want to define e.g. `nFinite n X` as a *small* proposition.
  -- (Possibly we don't really care.)
  FinCW : Type₀
  FinCW = Σ ℕ IndexedFinCW

  decodeFinCW : FinCW → Type₀
  decodeFinCW c = decodeIndexedFinCW (snd c)

-- finite CW complexes
postulate
  isFinCW : Type ℓ → Type ℓ
  isFinCW-isProp : {X : Type ℓ} → isProp (isFinCW X)

  isFinCW-def : {X : Type ℓ} → isFinCW X ≃ ∥ Σ[ C ∈ FinCW ] X ≡ Lift {j = ℓ} (decodeFinCW C) ∥₁

  -- closure under pushouts, products, etc.

  isFinCWUnit : isFinCW (Unit* {ℓ = ℓ})

  isFinCWSn : {n : ℕ} → isFinCW (S₊ n)

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
    → ∥ Σ[ l ∈ (X → Y) ] f ∘ l ≡ g ∥₁

  mapFromNSkel : (X : Type ℓ) (hX : isFinCW X) (n : HLevel)
    → ∥ Σ[ Y ∈ Type ℓ ] Σ[ hY ∈ isNDimFinCW n Y ] Σ[ f ∈ (X → Y) ] isConnectedFun n f ∥₁
