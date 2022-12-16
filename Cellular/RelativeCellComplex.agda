module Cellular.RelativeCellComplex where

open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Sigma
open import Cubical.Foundations.Everything
open import Cubical.Foundations.SIP
open import Cubical.HITs.Pushout
open import Cubical.HITs.PropositionalTruncation

open import Pushout.IsPushout
open import Pushout.More

private
  variable
    ℓi ℓ ℓ' : Level

-- We can give an equality of "types under a fixed type X"
-- by giving an Equiv and a commutative triangle.
≡under : {X Y Y' : Type ℓ} {f : X → Y} {f' : X → Y'}
  (g : Y ≃ Y') (h : equivFun g ∘ f ≡ f')
  → ( Y , f ) ≡ ( Y' , f' )
≡under {ℓ = ℓ} {X = X} {Y = Y} {Y' = Y'} {f = f} {f' = f'} g h =
  sip us (Y , f) (Y' , f') (g , h)
  where
    S : Type ℓ → Type ℓ
    S Z = X → Z

    ι : StrEquiv S ℓ
    ι A B e = equivFun e ∘ A .snd ≡ B .snd

    sns : SNS S ι
    sns A B = idEquiv _

    us : UnivalentStr S ι
    us = SNS→UnivalentStr ι sns

-- A collection of "basic cells", usually denoted ℐ = \McI.
-- A "relative ℐ-cell complex" will be a finite composition
-- of pushouts of morphisms belonging to ℐ.
record Family : Type (ℓ-max (ℓ-suc ℓi) (ℓ-suc ℓ)) where
  no-eta-equality
  field
    Ix : Type ℓi
    A B : Ix → Type ℓ
    j : (i : Ix) → A i → B i

module _ (ℐ : Family {ℓi = ℓi} {ℓ = ℓ}) where
  open Family ℐ

  -- A "relative ℐ-cell complex" with base `X : Type ℓ`
  -- will be defined as a relative ℐ-cell complex of length `n`
  -- for some `n : ℕ`, which we define first.

  module RCCOL where
    -- We define the following by simultaneous recursion on `n`:
    -- * `T`: The type of relative ℐ-cell complexes of length `n`
    --   and base `X`. These are "codes", that specify how
    --   a sequence of `n` ℐ-cells should be attached to `X`.
    -- * `cod`: Given a code as above, returns the codomain
    --   of the resulting relative ℐ-cell complex.
    -- * `fun`: Given a code as above, returns the actual map
    --   that is the relative ℐ-cell complex.
    --
    -- These recursive definitions could easily be translated to
    -- a single recursive definition of type
    --   ℕ → (X : Type ℓ) →
    --     Σ[ T ∈ Type (ℓ-max ℓi ℓ) ] Σ[ ty ∈ (T → Type ℓ) ] (X → ty).
    -- but it seems more convenient in Agda to define them separately.
    T : ℕ → Type ℓ → Type (ℓ-max ℓi ℓ)
    cod : {n : ℕ} {X : Type ℓ} → T n X → Type ℓ
    fun : {n : ℕ} {X : Type ℓ} (c : T n X) → (X → cod c)

    -- * For `n = 0`, there is a single complex of length `n`.
    --   (representing the function `id : X → X`).
    T 0 X = Unit*
    -- * A cell complex of length `m+1` consists of
    --     a first attaching map `k : A i → X` for some `i`,
    --     together with a cell complex of length `m`
    --     starting from the pushout of `k` and the cell `A i → B i`.
    --
    --           j i
    --        A i → B i
    --       k ↓     ↓ inl
    --         X  →  X'
    --           inr
    --
    --   (This might be less obvious than putting the "new cell"
    --   at the end, rather than the start;
    --   this choice seems to work out better.)
    T (suc m) X =
      Σ[ i ∈ Ix ] Σ[ k ∈ (A i → X) ] T m (Pushout (j i) k)

    cod {n = 0} {X} c = X
    cod {n = suc m} (i , k , c) = cod c

    fun {n = 0} {X} c = idfun X
    fun {n = suc m} (i , k , c) = fun c ∘ inr

    -- concatenation
    concat : {m n : ℕ} {X : Type ℓ} (c : T m X) (d : T n (cod c))
      → T (m + n) X
    concat {m = 0} c d = d
    concat {m = suc _} c d .fst = c .fst
    concat {m = suc _} c d .snd .fst = c .snd .fst
    concat {m = suc _} c d .snd .snd = concat (c .snd .snd) d

    -- `fun (concat c d)` equals `fun d ∘ fun c`,
    -- at least up to equivalence under `X`.
    funConcat : {m n : ℕ} {X : Type ℓ} (c : T m X) (d : T n (cod c))
      → Σ[ h ∈ cod (concat c d) ≃ cod d ]
          equivFun h ∘ fun (concat c d) ≡ fun d ∘ fun c
    funConcat {m = 0} c d .fst = idEquiv _
    funConcat {m = 0} c d .snd = refl
    funConcat {m = suc _} c d .fst = funConcat (c .snd .snd) d .fst
    funConcat {m = suc _} c d .snd =
      cong (_∘ inr) (funConcat (c .snd .snd) d .snd)

    -- pushout
    po : {n : ℕ} {X X' : Type ℓ} (g : X → X') → T n X → T n X'
    po {n = 0} _ _ = tt*
    po {n = suc m} _ c .fst = c .fst
    po {n = suc m} g c .snd .fst = g ∘ c .snd .fst
    po {n = suc m} g c .snd .snd =
      po (Pushout→ _ _ _ _ (idfun _) (idfun _) g refl refl) (c .snd .snd)

    -- `fun (po g c)` is a pushout along `g` of `fun c`.
    funPO : {n : ℕ} {X X' : Type ℓ} (g : X → X') (c : T n X)
      → isPushoutAlong (fun c) (fun (po g c)) g
    funPO {n = 0} g _ .fst = g
    funPO {n = 0} g _ .snd .fst = refl
    funPO {n = 0} g _ .snd .snd = idIsPushout'
    funPO {n = suc m} g c
--  TODO: Is it possible to use cancel-isPushoutAlong somehow?
--      isPushoutAlong-comp (cancel-isPushoutAlong isPushoutAlongInr isPushoutAlongInr)
--      (funPO _ {!c .snd .snd!})
--  Maybe would be better to define `po` and `funPO` simultaneously?
      with funPO (Pushout→ _ _ _ _ (idfun _) (idfun _) g refl refl) (c .snd .snd)
    ... | (h , α , po) = h , _ ,
      pasteIsPushout
        (cancel'IsPushout' {γ = refl} (funExt push)
          (PushoutIsPushout (j (c .fst)) (c .snd .fst))
          (PushoutIsPushout (j (c .fst)) (g ∘ c .snd .fst)) (rUnit _ ∙ rUnit _)) po

  module relativeCellComplex where
    T : Type ℓ → Type (ℓ-max ℓi ℓ)
    T X = Σ[ n ∈ ℕ ] RCCOL.T n X

    cod : {X : Type ℓ} → T X → Type ℓ
    cod (n , c) = RCCOL.cod c

    fun : {X : Type ℓ} → (c : T X) → X → cod c
    fun (n , c) = RCCOL.fun c

    concat : {X : Type ℓ} (c : T X) (d : T (cod c)) → T X
    concat c d .fst = c .fst + d .fst
    concat c d .snd = RCCOL.concat (c .snd) (d .snd)

    funConcat : {X : Type ℓ} (c : T X) (d : T (cod c))
      → Σ[ h ∈ cod (concat c d) ≃ cod d ]
          equivFun h ∘ fun (concat c d) ≡ fun d ∘ fun c
    funConcat c d = RCCOL.funConcat (c .snd) (d .snd)

    po : {X X' : Type ℓ} (g : X → X') → T X → T X'
    po g c .fst = c .fst
    po g c .snd = RCCOL.po g (c .snd)

    funPO : {X X' : Type ℓ} (g : X → X') (c : T X)
      → isPushoutAlong (fun c) (fun (po g c)) g
    funPO g c = RCCOL.funPO g (c .snd)

module _ (ℐ : Family {ℓi = ℓi} {ℓ = ℓ}) where
  open Family ℐ
  open relativeCellComplex ℐ

  -- A map `f : X → Y` "is a relative ℐ-cell complex" if it (merely)
  -- is of the form `fun c`, up to equivalence under `X`.
  isRelativeCellComplex : {X Y : Type ℓ} (f : X → Y) → Type (ℓ-max ℓi ℓ)
  isRelativeCellComplex {X = X} {Y = Y} f =
    ∥ Σ[ c ∈ T X ] Σ[ g ∈ (cod c ≃ Y) ] equivFun g ∘ fun c ≡ f ∥₁

  isPropIsRelativeCellComplex : {X Y : Type ℓ} {f : X → Y}
    → isProp (isRelativeCellComplex f)
  isPropIsRelativeCellComplex = isPropPropTrunc

  isRCC-fun : {X : Type ℓ} (c : T X) → isRelativeCellComplex (fun c)
  isRCC-fun c = ∣ c , idEquiv _ , refl ∣₁

  -- To prove that a proposition holds for all relative `ℐ`-cell complexes,
  -- it suffices to check that it holds for all maps of the form `fun c`.
  isRCC-ind : {X : Type ℓ} (C : {Y : Type ℓ} (f : X → Y) → Type ℓ')
    (hC : {Y : Type ℓ} (f : X → Y) → isProp (C f))
    (H : (c : T X) → C (fun c))
    → {Y : Type ℓ} (f : X → Y) (hf : isRelativeCellComplex f) → C f
  isRCC-ind {X = X} C hC H {Y} f hf = elim (λ _ → hC f)
    (λ ( c , h , k ) → (subst C' (≡under h k) (H c)))
    hf
    where
      C' : (Σ[ Y' ∈ Type ℓ ] (X → Y')) → Type _
      C' p = C (p .snd)

  -- The identity is a relative cell complex.
  isRCC-idfun : {X : Type ℓ} → isRelativeCellComplex (idfun X)
  isRCC-idfun = isRCC-fun (0 , tt*)

  -- An equivalence is a relative cell complex.
  isRCC-isEquiv : {X Y : Type ℓ} (f : X → Y) → isEquiv f → isRelativeCellComplex f
  isRCC-isEquiv f hf = ∣ ( 0 , tt* ) , ( f , hf ) , refl ∣₁

  isRCC-equiv : {X Y : Type ℓ} (f : X ≃ Y) → isRelativeCellComplex (equivFun f)
  isRCC-equiv f = isRCC-isEquiv (equivFun f) (f .snd)

  -- Relative cell complexes are closed under composition.
  isRCC-comp : {X Y Z : Type ℓ} {f : X → Y} {g : Y → Z}
    → isRelativeCellComplex f → isRelativeCellComplex g → isRelativeCellComplex (g ∘ f)
  isRCC-comp hf hg =
    isRCC-ind
      (λ {Y} f → {Z : Type ℓ} (g : Y → Z) →
        isRelativeCellComplex g → isRelativeCellComplex (g ∘ f))
      (λ f → isPropImplicitΠ λ _ → isPropΠ2 (λ _ _ → isPropIsRelativeCellComplex))
      (λ c →
        isRCC-ind
          (λ {Z} g → isRelativeCellComplex (λ x → g (fun c x)))
          (λ _ → isPropIsRelativeCellComplex)
          (λ d → ∣ concat c d , funConcat c d ∣₁))
    _ hf
    _ hg

  -- Relative cell complexes are closed under pushout.
  isRCC-po : {X Y X' Y' : Type ℓ} {f : X → Y} {f' : X' → Y'}
    → isPushoutOf f f'
    → isRelativeCellComplex f → isRelativeCellComplex f'
  isRCC-po ipo hf =
    isRCC-ind
      (λ {Y} f → {X' Y' : Type ℓ} (f' : X' → Y') → isPushoutOf f f' → isRelativeCellComplex f')
      (λ f → isPropImplicitΠ2 λ _ _ → isPropΠ2 λ _ _ → isPropIsRelativeCellComplex)
      (λ c f' (g , g' , α , hpo) →
        pushoutRec' _ g {Z = λ g' f' α → isRelativeCellComplex f'}
          _ _ _ (funPO g c .snd .snd) (isRCC-fun (po g c))
          g' f' α hpo)
    _ hf _ ipo

  -- The maps of ℐ are relative ℐ-cell complexes.
  isRCC-base : (i : Ix) → isRelativeCellComplex (j i)
  isRCC-base i = ∣ (1 , i , idfun _ , tt*) , Pushout-id-≃ _ , refl ∣₁

  -- Elimination principle:
  -- To prove a property for all relative ℐ-cell complexes,
  -- it suffices to check that it holds for the maps of ℐ
  -- and is preserved under (nullary and binary) composition
  -- and pushouts.
  module _
    (P : {X Y : Type ℓ} (f : X → Y) → Type ℓ')
    (hP : {X Y : Type ℓ} (f : X → Y) → isProp (P f))
    (hP₀ : {X : Type ℓ} → P (idfun X))
    (hP₂ : {X Y Z : Type ℓ} (f : X → Y) (g : Y → Z)
      → P f → P g → P (g ∘ f))
    (hP₁ : {i : Ix} → P (j i))
    (hPpo : {X Y X' : Type ℓ} (f : X → Y) (k : X → X')
      → P f → P (Pushout.inr {f = f} {g = k})) where

    elimRCCOL : {n : ℕ} {X : Type ℓ} (c : RCCOL.T ℐ n X) → P (RCCOL.fun ℐ c)
    elimRCCOL {n = 0} c = hP₀
    elimRCCOL {n = suc m} c =
      hP₂ _ _ (hPpo _ _ hP₁) (elimRCCOL (c .snd .snd))

    elimRCC : {X : Type ℓ} (c : T X) → P (fun c)
    elimRCC ( n , c ) = elimRCCOL c

    isRCCElimProp :
      {X Y : Type ℓ} (f : X → Y) (hf : isRelativeCellComplex f) → P f
    isRCCElimProp {X = X} {Y = Y} f = rec (hP _) λ ( c , h ) →
      subst (λ p → P (p .snd)) (≡under (h .fst) (h .snd)) (elimRCC c)

-- Change of family.
-- If every morphism of ℐ' is a relative ℐ-cell complex,
-- then so is every relative ℐ'-cell complex.
module _ (ℐ ℐ' : Family {ℓi = ℓi} {ℓ = ℓ}) where
  open Family

  FamilyGenerates : Type _
  FamilyGenerates = (i' : Ix ℐ') → isRelativeCellComplex ℐ (j ℐ' i')

  isRCC-familyGenerates : FamilyGenerates → {X Y : Type ℓ} {f : X → Y}
    → isRelativeCellComplex ℐ' f → isRelativeCellComplex ℐ f
  isRCC-familyGenerates fg = isRCCElimProp ℐ' (isRelativeCellComplex ℐ)
    (λ f → isPropIsRelativeCellComplex ℐ) (isRCC-idfun ℐ) (λ f g → isRCC-comp ℐ)
    (fg _) (λ f k hf → isRCC-po ℐ isPushoutOfInr hf) _
