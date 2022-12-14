module Cellular.Fold where

open import Cubical.Data.Sigma
open import Cubical.Foundations.Everything
open import Cubical.HITs.Pushout

open import Cellular.RelativeCellComplex
open import Pushout.IsPushout
open import Pushout.Fold

private
  variable
    ℓi ℓ ℓ' : Level

module _ (ℐ : Family {ℓi = ℓi} {ℓ = ℓ}) where
  open Family
  foldFamily : Family {ℓi = ℓi} {ℓ = ℓ}
  Ix foldFamily = Ix ℐ
  A foldFamily i = Pushout (j ℐ i) (j ℐ i)
  B foldFamily i = B ℐ i
  j foldFamily i = fold (j ℐ i)

  private
    -- This would hold for any family, not just `foldFamily`.
    isRCC-FF-comp : {X Y Z : Type ℓ} (f : X → Y) (g : Y → Z)
      → isRelativeCellComplex foldFamily (fold f)
      → isRelativeCellComplex foldFamily (fold g)
      → isRelativeCellComplex foldFamily (fold (g ∘ f))
    isRCC-FF-comp f g hf hg with task2 f g
    ... | (h , e , ipo) = subst (isRelativeCellComplex foldFamily) (sym e)
      (isRCC-comp _ (isRCC-po _ ipo hf) hg)

  foldComplex : {X Y : Type ℓ} (f : X → Y) → isRelativeCellComplex ℐ f
    → isRelativeCellComplex foldFamily (fold f)
  foldComplex = isRCCElimProp ℐ
    (λ f → isRelativeCellComplex foldFamily (fold f))
    (λ f → isPropIsRelativeCellComplex _)
    (λ {X} → isRCC-isEquiv _ _ isEquiv-fold-id)
    (isRCC-FF-comp)
    (isRCC-base _ _)
    λ f k hf → isRCC-po _ (task1 isPushoutOfInr) hf

  -- ℐ is "self-folding" if for any `f ∈ ℐ`,
  -- `fold f` is a relative ℐ-cell complex.
  -- For example, ℐ = {Sⁿ → 1 | n ≥ N} has this property.
  SelfFolding : Type _
  SelfFolding = FamilyGenerates ℐ foldFamily

  -- If ℐ is self-folding, then relative ℐ-cell complexes
  -- have a cancellation property.
  module _ (sf : SelfFolding) {Z A B : Type ℓ} (f : Z → A) (g : A → B) where
    cancelRCC-R :
        isRelativeCellComplex ℐ f
      → isRelativeCellComplex ℐ (g ∘ f)
      → isRelativeCellComplex ℐ g
    cancelRCC-R hf hgf =
      isRCC-comp _
      (isRCC-po _ isPushoutOfInl hgf)
      (isRCC-po _ i (isRCC-familyGenerates _ _ sf (foldComplex f hf)))
      where
        cf : Pushout f (g ∘ f) → B
        cf (inl a) = g a
        cf (inr b) = b
        cf (push z i) = g (f z)

        i : isPushoutOf (fold f) cf
        i .fst = FoldStuff.Pushout→₂ f f g
        i .snd .fst = g
        i .snd .snd .fst j (inl a) = g a
        i .snd .snd .fst j (inr a) = g a
        i .snd .snd .fst j (push z k) = g (f z)
        i .snd .snd .snd =
          cancelIsPushout {g = g} {β = refl}
            (cancel'IsPushout' (funExt push)
              (PushoutIsPushout f f)
              (PushoutIsPushout f (g ∘ f))
              (rUnit _))
            (equivIsPushout' (idIsEquiv A) (idIsEquiv B))
