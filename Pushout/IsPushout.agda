module Pushout.IsPushout where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma
open import Cubical.HITs.Pushout

private
  variable
    ℓ ℓ' ℓ'' : Level

-- TODO: Move these somewhere else

transportRefl' : {A : Type ℓ} → transport refl ≡ idfun A
transportRefl' = funExt transportRefl

module _ {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {f : A → B} {g : B → C} where
  compIsEquiv : isEquiv f → isEquiv g → isEquiv (g ∘ f)
  compIsEquiv hf hg = snd (compEquiv (_ , hf) (_ , hg))

  cancelEquivL : isEquiv g → isEquiv (g ∘ f) → isEquiv f
  cancelEquivL hg = isEquiv[equivFunA≃B∘f]→isEquiv[f] f (g , hg)

  cancelEquivR : isEquiv f → isEquiv (g ∘ f) → isEquiv g
  cancelEquivR hf = isEquiv[f∘equivFunA≃B]→isEquiv[f] g (f , hf)

-- TODO: Move to separate file (Whiskering)

_◃_ : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (f : B → C) {g g' : A → B} (α : g ≡ g') → f ∘ g ≡ f ∘ g'
f ◃ α = cong (f ∘_) α

_▹_ : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {f f' : B → C} (α : f ≡ f') (g : A → B) → f ∘ g ≡ f' ∘ g
α ▹ g = cong (_∘ g) α

module _ {A B C : Type ℓ} (f : A → B) (g : A → C) where
  SpanCoconeOn : Type ℓ → Type ℓ
  SpanCoconeOn D = Σ[ g' ∈ (B → D) ] Σ[ f' ∈ (C → D) ] g' ∘ f ≡ f' ∘ g

  module SpanCoconeOn {D : Type ℓ} (sco : SpanCoconeOn D) where
    g' : B → D
    g' = sco .fst

    f' : C → D
    f' = sco .snd .fst

    α' : g' ∘ f ≡ f' ∘ g
    α' = sco .snd .snd

  postcomp : {D D' : Type ℓ} → (D → D') → SpanCoconeOn D → SpanCoconeOn D'
  postcomp h sco .fst = h ∘ sco .fst
  postcomp h sco .snd .fst = h ∘ sco .snd .fst
  postcomp h sco .snd .snd = h ◃ sco .snd .snd

  postcomp-id : {D : Type ℓ} → postcomp (idfun D) ≡ idfun _
  postcomp-id = refl

  postcomp-transport : {D D' : Type ℓ} (p : D ≡ D') →
    postcomp (transport p) ≡ transport (λ i → SpanCoconeOn (p i))
  postcomp-transport {D = D} {D' = D'} =
    J (λ (D' : Type ℓ) (p : D ≡ D') → postcomp (transport p) ≡ transport (cong SpanCoconeOn p))
    (cong postcomp transportRefl' ∙∙ postcomp-id ∙∙ sym transportRefl')

  module _ {P : Type ℓ} (g' : B → P) (f' : C → P) (α : g' ∘ f ≡ f' ∘ g) where
    pushoutComparison : (E : Type ℓ) → (P → E) → SpanCoconeOn E
    pushoutComparison E h = postcomp h (g' , f' , α)

    record isPushout : Type (ℓ-suc ℓ) where
      no-eta-equality
      field
        comparisonIsEquiv : (E : Type ℓ) → isEquiv (pushoutComparison E)

    open isPushout

    isPropIsPushout : isProp isPushout
    comparisonIsEquiv (isPropIsPushout po po' i) =
      isPropΠ (λ E → isPropIsEquiv _) (po .comparisonIsEquiv) (po' .comparisonIsEquiv) i

  open isPushout

  -- The HIT `Pushout f g` is a pushout

  PushoutIsPushout : isPushout {P = Pushout f g} inl inr (funExt push)
  comparisonIsEquiv PushoutIsPushout E = isoToIsEquiv i
    where
      open Iso
      i : Iso (Pushout f g → E) _
      i .fun = pushoutComparison inl inr (funExt push) E
      i .inv s (inl b) = s .fst b
      i .inv s (inr c) = s .snd .fst c
      i .inv s (push a k) = s .snd .snd k a
      i .rightInv s = refl
      i .leftInv h j (inl b) = h (inl b)
      i .leftInv h j (inr c) = h (inr c)
      i .leftInv h j (push a k) = h (push a k)

  SpanCocone : Type (ℓ-suc ℓ)
  SpanCocone = Σ (Type ℓ) SpanCoconeOn

  PushoutSC : SpanCocone
  PushoutSC .fst = Pushout f g
  PushoutSC .snd .fst = inl
  PushoutSC .snd .snd .fst = inr
  PushoutSC .snd .snd .snd = funExt push

  module SpanCocone (sc : SpanCocone) where
    open SpanCoconeOn (sc .snd) public

    D : Type ℓ
    D = sc .fst

    SCIsPushout : Type (ℓ-suc ℓ)
    SCIsPushout = isPushout g' f' α'

  module _ {D₁ D₂ : Type ℓ} (sco₁ : SpanCoconeOn D₁) (sco₂ : SpanCoconeOn D₂) (h : D₁ → D₂) where
    open SpanCoconeOn sco₁ renaming (g' to g₁ ; f' to f₁ ; α' to α₁)
    open SpanCoconeOn sco₂ renaming (g' to g₂ ; f' to f₂ ; α' to α₂)

    SpanCoconeHomOver : Type ℓ
    SpanCoconeHomOver =
      Σ[ pg ∈ g₂ ≡ h ∘ g₁ ] Σ[ pf ∈ h ∘ f₁ ≡ f₂ ] (pg ▹ f) ∙∙ (h ◃ α₁) ∙∙ (pf ▹ g) ≡ α₂

    ≡≃SCHO : (postcomp h sco₁ ≡ sco₂) ≃ SpanCoconeHomOver
    ≡≃SCHO =
        ((h ∘ g₁ , h ∘ f₁ , h ◃ α₁) ≡ sco₂)
      ≃⟨ compEquiv (invEquiv ΣPath≃PathΣ) (Σ-cong-equiv-snd (λ pg' → invEquiv ΣPath≃PathΣ)) ⟩
        Σ[ pg' ∈ h ∘ g₁ ≡ g₂ ] Σ[ pf ∈ h ∘ f₁ ≡ f₂ ] PathP (λ i → pg' i ∘ f ≡ pf i ∘ g) (h ◃ α₁) α₂
      ≃⟨ Σ-cong-equiv-fst (isoToEquiv symIso) ⟩
        Σ[ pg ∈ g₂ ≡ h ∘ g₁ ] Σ[ pf ∈ h ∘ f₁ ≡ f₂ ] PathP (λ i → pg (~ i) ∘ f ≡ pf i ∘ g) (h ◃ α₁) α₂
      ≃⟨ Σ-cong-equiv-snd (λ pg → Σ-cong-equiv-snd (λ pf →
           pathToEquiv (PathP≡doubleCompPathˡ (cong (_∘ f) (sym pg)) (h ◃ α₁) α₂ (cong (_∘ g) pf)))) ⟩
        SpanCoconeHomOver
      ■

    -- If h is an equivalence, we can even build a path sco₁ ≡ sco₂
    -- from h together with a SpanCoconeHomOver h.
    ≡-of-SCHO : (eh : isEquiv h) → SpanCoconeHomOver → PathP (λ i → SpanCoconeOn (ua (h , eh) i)) sco₁ sco₂
    ≡-of-SCHO eh scho = toPathP
      (sym (postcomp-transport (ua (h , eh)) ≡$ sco₁) ∙
       cong (λ f₁ → postcomp f₁ sco₁) (funExt (uaβ (h , eh))) ∙
       invEq ≡≃SCHO scho)

  idSCHO : {D : Type ℓ} {sco : SpanCoconeOn D} → SpanCoconeHomOver sco sco (idfun D)
  idSCHO = fst (≡≃SCHO _ _ (idfun _)) refl

  compSCHO : {D₁ D₂ D₃ : Type ℓ} {sco₁ : SpanCoconeOn D₁} {sco₂ : SpanCoconeOn D₂} {sco₃ : SpanCoconeOn D₃}
    (h₁₂ : D₁ → D₂) (h₂₃ : D₂ → D₃) → SpanCoconeHomOver sco₁ sco₂ h₁₂ → SpanCoconeHomOver sco₂ sco₃ h₂₃
    → SpanCoconeHomOver sco₁ sco₃ (h₂₃ ∘ h₁₂)
  compSCHO h₁₂ h₂₃ scho₁₂ scho₂₃ =
    fst (≡≃SCHO _ _ (h₂₃ ∘ h₁₂)) (cong (postcomp h₂₃) (invEq (≡≃SCHO _ _ h₁₂) scho₁₂) ∙ (invEq (≡≃SCHO _ _ h₂₃) scho₂₃))

  module _ {D' : Type ℓ} (sc : SpanCocone) (i : Iso (sc .fst) D') where
    ≡-of-Iso : sc ≡ (D' , postcomp (i .Iso.fun) (sc .snd))
    ≡-of-Iso = ΣPathP (ua (isoToEquiv i) , ≡-of-SCHO (sc .snd) (postcomp (i .Iso.fun) (sc .snd)) (i .Iso.fun) (isoToIsEquiv i) idSCHO)

  module _ {P P' : Type ℓ} {g' : B → P} {f' : C → P} {α : g' ∘ f ≡ f' ∘ g} (i : Iso P P') where
    isPushoutOfIsoIsPushout : isPushout g' f' α → isPushout (i .Iso.fun ∘ g') (i .Iso.fun ∘ f') (i .Iso.fun ◃ α)
    isPushoutOfIsoIsPushout po = subst SpanCocone.SCIsPushout (≡-of-Iso (P , g' , f' , α) i) po

  -- Induced map out of the pushout

  module _ {sc₁ : SpanCocone} (po : SpanCocone.SCIsPushout sc₁) (sc₂ : SpanCocone) where
    open isPushout
    open SpanCocone sc₁ renaming (D to D₁ ; g' to g₁ ; f' to f₁ ; α' to α₁)
    open SpanCocone sc₂ renaming (D to D₂ ; g' to g₂ ; f' to f₂ ; α' to α₂)

    inducedContr : isContr (Σ (D₁ → D₂) (SpanCoconeHomOver (sc₁ .snd) (sc₂ .snd)))
    inducedContr = subst isContr (ua (Σ-cong-equiv-snd (λ h → ≡≃SCHO _ _ h)))
      (equiv-proof (comparisonIsEquiv po D₂) (sc₂ .snd))

    induced : Σ (D₁ → D₂) (SpanCoconeHomOver (sc₁ .snd) (sc₂ .snd))
    induced = inducedContr .fst

    inducedUniq : (h h' : D₁ → D₂)
      → SpanCoconeHomOver (sc₁ .snd) (sc₂ .snd) h
      → SpanCoconeHomOver (sc₁ .snd) (sc₂ .snd) h'
      → h ≡ h'                  -- The `SpanCoconeHomOver`s are equal too, but we don't need this.
    inducedUniq h h' scho scho' = cong fst (isContr→isProp inducedContr (h , scho) (h' , scho'))

  -- Uniqueness of pushout (up to isomorphism / a path)

  module _ {sc₁ sc₂ : SpanCocone} (po₁ : SpanCocone.SCIsPushout sc₁) (po₂ : SpanCocone.SCIsPushout sc₂) where
    open SpanCocone
    private
      open Iso
      h₁₂ : D sc₁ → D sc₂
      h₁₂ = induced po₁ sc₂ .fst

      h₂₁ : D sc₂ → D sc₁
      h₂₁ = induced po₂ sc₁ .fst

      i : Iso (D sc₁) (D sc₂)
      i .fun = h₁₂
      i .inv = h₂₁
      i .rightInv = funExt⁻
        (inducedUniq po₂ sc₂ (h₁₂ ∘ h₂₁) (idfun (D sc₂)) (compSCHO h₂₁ h₁₂ (induced po₂ sc₁ .snd) (induced po₁ sc₂ .snd)) idSCHO)
      i .leftInv = funExt⁻
        (inducedUniq po₁ sc₁ (h₂₁ ∘ h₁₂) (idfun (D sc₁)) (compSCHO h₁₂ h₂₁ (induced po₁ sc₂ .snd) (induced po₂ sc₁ .snd)) idSCHO)

      pD : D sc₁ ≡ D sc₂
      pD = ua (isoToEquiv i)

    pushoutUnique : sc₁ ≡ sc₂
    pushoutUnique = ΣPathP (pD , ≡-of-SCHO (sc₁ .snd) (sc₂ .snd) h₁₂ (isoToIsEquiv i) (induced po₁ sc₂ .snd))

  -- Any pushout is equal to Pushout
  pushoutIsPushout : {sc : SpanCocone} (po : SpanCocone.SCIsPushout sc) → PushoutSC ≡ sc
  pushoutIsPushout = pushoutUnique PushoutIsPushout

  pushoutRec' : {Z : {P : Type ℓ} (g' : B → P) (f' : C → P) (α : g' ∘ f ≡ f' ∘ g) → Type ℓ'} →
    {P0 : Type ℓ} (g'0 : B → P0) (f'0 : C → P0) (α0 : g'0 ∘ f ≡ f'0 ∘ g) (po0 : isPushout g'0 f'0 α0) → Z g'0 f'0 α0 →
    {P : Type ℓ} (g' : B → P) (f' : C → P) (α : g' ∘ f ≡ f' ∘ g) (po : isPushout g' f' α) → Z g' f' α
  pushoutRec' {Z = Z} g'0 f'0 α0 po0 hZ g' f' α po = subst Z' (pushoutUnique po0 po) hZ
    where
      Z' : SpanCocone → Type _
      Z' sc = Z (sc .snd .fst) (sc .snd .snd .fst) (sc .snd .snd .snd)

  -- Induction principle for pushouts:
  -- to prove a property for any pushout diagram,
  -- it suffices to prove it for Pushout.
  pushoutRec : {Z : {P : Type ℓ} (g' : B → P) (f' : C → P) (α : g' ∘ f ≡ f' ∘ g) → Type ℓ'} →
    Z {P = Pushout f g} inl inr (funExt push) →
    {P : Type ℓ} (g' : B → P) (f' : C → P) (α : g' ∘ f ≡ f' ∘ g) (po : isPushout g' f' α) → Z g' f' α
  pushoutRec {Z = Z} hZ = pushoutRec' {Z = Z} {P0 = Pushout f g} inl inr (funExt push) PushoutIsPushout hZ

open isPushout

-- Facts about pushouts.

-- The transpose of a pushout square is a pushout.
transposeIsPushout : {A B C P : Type ℓ} {f : A → B} {g : A → C} {g' : B → P} {f' : C → P} {α : g' ∘ f ≡ f' ∘ g} →
  isPushout f g g' f' α → isPushout g f f' g' (sym α)
transposeIsPushout {f = f} {g = g} po .comparisonIsEquiv E =
  compIsEquiv (po .comparisonIsEquiv E) (isoToIsEquiv i)
  where
    open Iso
    i : Iso (SpanCoconeOn f g E) (SpanCoconeOn g f E)
    i .fun sco .fst = sco .snd .fst
    i .fun sco .snd .fst = sco .fst
    i .fun sco .snd .snd = sym (sco .snd .snd)
    i .inv sco .fst = sco .snd .fst
    i .inv sco .snd .fst = sco .fst
    i .inv sco .snd .snd = sym (sco .snd .snd)
    i .rightInv sco = refl
    i .leftInv sco = refl

{-
  Any square whatsoever
      f
    A → B
  g ↓ α ↓ g'
    C → D
      f'
  in which g & g' are equivalences is a pushout.
-}
{-
  Why: Because for any E, the map sending a cocone (g'' , f'' , β) on E to its component g''
  is an equivalence (as f'' & β are then determined by canceling g in β : g'' ∘ f ≡ f'' ∘ g);
  and then the map sending (h : D → E) to g'' = h ∘ g' is an equivalence, by canceling g'.
-}
module _ {A B C D : Type ℓ} {f : A → B} {g : A → C} {g' : B → D} {f' : C → D} {α : g' ∘ f ≡ f' ∘ g} where
  equivIsPushout : isEquiv g → isEquiv g' → isPushout f g g' f' α
  equivIsPushout hg hg' .comparisonIsEquiv E =
    cancelEquivL e₁ e₂
    where
      e₀ : isEquiv (λ (f₁ : C → E) → f₁ ∘ g)
      e₀ = isEquivPreComp (g , hg)

      hcontr : (g'' : B → E) → isContr (Σ[ f'' ∈ (C → E) ] (g'' ∘ f ≡ f'' ∘ g))
      hcontr g'' = subst isContr (Σ-cong-snd λ _ → isoToPath symIso) (e₀ .equiv-proof (g'' ∘ f))

      e₁ : isEquiv (λ (sc : SpanCoconeOn f g E) → sc .fst)
      e₁ = snd (Σ-contractSnd hcontr)

      e₂ : isEquiv (λ (h : D → E) → h ∘ g')
      e₂ = isEquivPreComp (g' , hg')

-- Same as above, but for squares in which the horizontal morphisms are equivalences.
module _ {A B C D : Type ℓ} {f : A → B} {g : A → C} {g' : B → D} {f' : C → D} {α : g' ∘ f ≡ f' ∘ g} where
  equivIsPushout' : isEquiv f → isEquiv f' → isPushout f g g' f' α
  equivIsPushout' hf hf' = transposeIsPushout (equivIsPushout {α = sym α} hf hf')

-- Frequently useful special case
module _ {A B : Type ℓ} {f : A → B} where
  idIsPushout : isPushout f (idfun A) (idfun B) f refl
  idIsPushout = equivIsPushout (idIsEquiv _) (idIsEquiv _)

  idIsPushout' : isPushout (idfun A) f f (idfun B) refl
  idIsPushout' = equivIsPushout' (idIsEquiv _) (idIsEquiv _)

{-
  Pushout pasting/cancellation.

      f₀    f₁
    A  →  A' → A''
  g ↓ β g'↓  γ ↓ g''
    B  →  B' → B''
      f'₀   f'₁
-}
module _ {A A' A'' B : Type ℓ} {f₀ : A → A'} {f₁ : A' → A''} {g : A → B} where
  private                       -- Build the iterated Pushout, which is known to be a pushout already.
    B₁ = Pushout f₀ g
    g₁ : A' → B₁
    g₁ = inl

    B₂ = Pushout f₁ g₁
    g₂ : A'' → B₂
    g₂ = inl

    b₀ : B → B₁
    b₀ = inr

    b₁ : B₁ → B₂
    b₁ = inr

    pastePushout : isPushout (f₁ ∘ f₀) g g₂ (b₁ ∘ b₀) ((funExt push ▹ f₀) ∙ (inr ◃ funExt push))
    pastePushout =
      isPushoutOfIsoIsPushout _ _ (invIso (PushoutDistr.PushoutDistrIso f₁ f₀ g)) (PushoutIsPushout _ _)

  module _ {B' B'' : Type ℓ} {g' : A' → B'} {g'' : A'' → B''}
    {f'₀ : B → B'} {f'₁ : B' → B''} {β : g' ∘ f₀ ≡ f'₀ ∘ g} {γ : g'' ∘ f₁ ≡ f'₁ ∘ g'} where

    pasteIsPushout :
      isPushout f₀ g g' f'₀ β → isPushout f₁ g' g'' f'₁ γ →
      isPushout (f₁ ∘ f₀) g g'' (f'₁ ∘ f'₀) ((γ ▹ f₀) ∙ (f'₁ ◃ β))
    pasteIsPushout po₀ po₁ =
      pushoutRec f₀ g
        {Z = λ {B' : Type ℓ} (g' : A' → B') (f'₀ : B → B') (β : g' ∘ f₀ ≡ f'₀ ∘ g) →
             {B'' : Type ℓ} {g'' : A'' → B''} {f'₁ : B' → B''} {γ : g'' ∘ f₁ ≡ f'₁ ∘ g'} →
             isPushout f₁ g' g'' f'₁ γ → isPushout (f₁ ∘ f₀) g g'' (f'₁ ∘ f'₀) ((γ ▹ f₀) ∙ (f'₁ ◃ β))}
        (λ {B'' = B''} {g'' = g''} {f'₁ = f'₁} {γ = γ} →
          pushoutRec _ _
            {Z = λ {B'' : Type ℓ} (g'' : A'' → B'') (f'₁ : Pushout f₀ g → B'') (γ : g'' ∘ f₁ ≡ f'₁ ∘ inl) →
                 isPushout (f₁ ∘ f₀) g g'' (f'₁ ∘ inr) (((γ ▹ f₀) ∙ (f'₁ ◃ funExt push)))}
            pastePushout _ _ _)
        _ _ _ po₀ po₁

  module _ {B' B'' : Type ℓ} {g' : A' → B'} {g'' : A'' → B''}
    {f'₀ : B → B'} {f'₁ : B' → B''} {β : g' ∘ f₀ ≡ f'₀ ∘ g} {γ : g'' ∘ f₁ ≡ f'₁ ∘ g'} where

    -- Auxiliary definitions for deducing cancellation from pasting.
    -- This is indirect, but maybe still easier than proving the pasting/cancellation laws directly,
    -- without using PushoutDistrIso.

    private
      module _ (E : Type ℓ) where
        C : SpanCoconeOn f₁ g' E → SpanCoconeOn (f₁ ∘ f₀) g E
        C sco .fst = sco .fst
        C sco .snd .fst = sco .snd .fst ∘ f'₀
        C sco .snd .snd = (sco .snd .snd ▹ f₀) ∙ (sco .snd .fst ◃ β)

        comm : {B''' : Type ℓ} (g'' : A'' → B''') (f'₁ : B' → B''') (γ : g'' ∘ f₁ ≡ f'₁ ∘ g') →
          pushoutComparison (f₁ ∘ f₀) g g'' (f'₁ ∘ f'₀) ((γ ▹ f₀) ∙ (f'₁ ◃ β)) E ≡ C ∘ pushoutComparison f₁ g' g'' f'₁ γ E
        comm g'' f'₁ γ i h .fst = h ∘ g''
        comm g'' f'₁ γ i h .snd .fst = h ∘ f'₁ ∘ f'₀
        comm g'' f'₁ γ i h .snd .snd = cong-∙ (h ∘_) (γ ▹ f₀) (f'₁ ◃ β) i

    -- When the left square is a pushout, C (which does not depend on B'' etc.) is an equivalence.
    -- We can prove this by forming a pushout square on the right, and using pasteIsPushout.
    -- Then use this to prove that if the original rectangle is a pushout, so is the right square.

    cancelIsPushout :
      isPushout f₀ g g' f'₀ β →
      isPushout (f₁ ∘ f₀) g g'' (f'₁ ∘ f'₀) ((γ ▹ f₀) ∙ (f'₁ ◃ β)) →
      isPushout f₁ g' g'' f'₁ γ
    cancelIsPushout po₀ po₂ .comparisonIsEquiv E =
      cancelEquivL hC (subst isEquiv (comm E g'' f'₁ γ) (po₂ .comparisonIsEquiv E))
      where
        po'₁ : isPushout f₁ g' inl inr (funExt push)
        po'₁ = PushoutIsPushout f₁ g'

        po'₀₁ = pasteIsPushout po₀ po'₁

        hC : isEquiv (C E)
        hC = cancelEquivR (po'₁ .comparisonIsEquiv E) (subst isEquiv (comm E inl inr (funExt push)) (po'₀₁ .comparisonIsEquiv E))

    -- Version with baked-in subst, since frequently
    -- the 2-cells will not automatically line up exactly
    -- (e.g., they differ by an `lUnit` or `rUnit`).
    cancelIsPushout' : (δ : g'' ∘ f₁ ∘ f₀ ≡ f'₁ ∘ f'₀ ∘ g)
      → isPushout f₀ g g' f'₀ β → isPushout (f₁ ∘ f₀) g g'' (f'₁ ∘ f'₀) δ
      → δ ≡ (γ ▹ f₀) ∙ (f'₁ ◃ β)
      → isPushout f₁ g' g'' f'₁ γ
    cancelIsPushout' δ po₀ po₂ η =
      cancelIsPushout po₀ (subst (isPushout _ _ _ _) η po₂)

-- Transposed pushout pasting/cancellation
module _ {A A' A'' B B' B'' : Type ℓ} {f₀ : A → A'} {f₁ : A' → A''} {g : A → B} {g' : A' → B'} {g'' : A'' → B''}
    {f'₀ : B → B'} {f'₁ : B' → B''} {β : f'₀ ∘ g ≡ g' ∘ f₀} {γ : f'₁ ∘ g' ≡ g'' ∘ f₁} where
  paste'IsPushout : isPushout g f₀ f'₀ g' β → isPushout g' f₁ f'₁ g'' γ
    → isPushout g (f₁ ∘ f₀) (f'₁ ∘ f'₀) g'' ((f'₁ ◃ β) ∙ (γ ▹ f₀))
  paste'IsPushout po₀ po₁ =
    subst (isPushout g (f₁ ∘ f₀) (f'₁ ∘ f'₀) g'') (symDistr (sym (γ ▹ f₀)) (sym (f'₁ ◃ β)))
    (transposeIsPushout (pasteIsPushout (transposeIsPushout po₀) (transposeIsPushout po₁)))

  cancel'IsPushout : isPushout g f₀ f'₀ g' β → isPushout g (f₁ ∘ f₀) (f'₁ ∘ f'₀) g'' ((f'₁ ◃ β) ∙ (γ ▹ f₀))
    → isPushout g' f₁ f'₁ g'' γ
  cancel'IsPushout po₀ po₂ =
    transposeIsPushout {α = sym γ} (cancelIsPushout (transposeIsPushout po₀) po'₂)
    where
      po'₂ : isPushout (f₁ ∘ f₀) g g'' (f'₁ ∘ f'₀) (sym (γ ▹ f₀) ∙ sym (f'₁ ◃ β))
      po'₂ = subst (isPushout (f₁ ∘ f₀) g g'' (f'₁ ∘ f'₀)) (symDistr (f'₁ ◃ β) (γ ▹ f₀)) (transposeIsPushout po₂)

  cancel'IsPushout' : (δ : f'₁ ∘ f'₀ ∘ g ≡ g'' ∘ f₁ ∘ f₀)
    → isPushout g f₀ f'₀ g' β → isPushout g (f₁ ∘ f₀) (f'₁ ∘ f'₀) g'' δ
    → δ ≡ ((f'₁ ◃ β) ∙ (γ ▹ f₀))
    → isPushout g' f₁ f'₁ g'' γ
  cancel'IsPushout' δ po₀ po₂ η =
    cancel'IsPushout po₀ (subst (isPushout _ _ _ _) η po₂)

module _ {A B A' B' : Type ℓ} where
  isPushoutAlong : (A → B) → (A' → B') → (A → A') → Type _
  isPushoutAlong f f' g = Σ[ g' ∈ (B → B') ] Σ[ α ∈ g' ∘ f ≡ f' ∘ g ] isPushout f g g' f' α

  ipaOfPO : {f : A → B} {f' : A' → B'} {g : A → A'} {g' : B → B'} {α : g' ∘ f ≡ f' ∘ g} →
    isPushout f g g' f' α → isPushoutAlong f f' g
  ipaOfPO po .fst = _
  ipaOfPO po .snd .fst = _
  ipaOfPO po .snd .snd = po

  isPushoutOf : (A → B) → (A' → B') → Type _
  isPushoutOf f f' = Σ (A → A') (isPushoutAlong f f')

  ipoOfPO : {f : A → B} {f' : A' → B'} {g : A → A'} {g' : B → B'} {α : g' ∘ f ≡ f' ∘ g} →
    isPushout f g g' f' α → isPushoutOf f f'
  ipoOfPO po .fst = _
  ipoOfPO po .snd .fst = _
  ipoOfPO po .snd .snd .fst = _
  ipoOfPO po .snd .snd .snd = po

  poOfIPO : {f : A → B} {f' : A' → B'} → (ipo : isPushoutOf f f') → isPushout f (ipo .fst) (ipo .snd .fst) f' (ipo .snd .snd .fst)
  poOfIPO ipo = ipo .snd .snd .snd

  -- These are not propositions.

isPushoutAlongSelf : {A B : Type ℓ} (f : A → B) → isPushoutAlong f f (idfun A)
isPushoutAlongSelf {A = A} {B = B} f = ipaOfPO (equivIsPushout {α = refl} (idIsEquiv A) (idIsEquiv B))

isPushoutOfSelf : {A B : Type ℓ} (f : A → B) → isPushoutOf f f
isPushoutOfSelf {A = A} {B = B} f .fst = idfun A
isPushoutOfSelf {A = A} {B = B} f .snd = isPushoutAlongSelf f

-- TODO: comp-isPushoutAlong, isPushoutAlong-comp

-- isPushoutAlong-comp : {A B C A' B' C' : Type ℓ} {f₀ : A → B} {f₁ : B → C} {f'₀ : A' → B'} {f'₁ : B' → C'} {g : A → A'}
--   → (ipa : isPushoutAlong f₀ f'₀ g) → isPushoutAlong f₁ f'₁ (ipa .fst) → isPushoutAlong (f₁ ∘ f₀) (f'₁ ∘ f'₀) g
-- isPushoutAlong-comp = _

-- Surprisingly nontrivial
cancel-isPushoutAlong' : {A B A' B' A'' B'' : Type ℓ} {f : A → B} {f' : A' → B'} {f'' : A'' → B''}
  {g₀ : A → A'} {g₁ : A' → A''} {g'₀ : B → B'} {g'₀₁ : B → B''} {α₀ : g'₀ ∘ f ≡ f' ∘ g₀} {α₀₁ : g'₀₁ ∘ f ≡ f'' ∘ g₁ ∘ g₀}
  → isPushout f g₀ g'₀ f' α₀ → isPushout f (g₁ ∘ g₀) g'₀₁ f'' α₀₁
  → Σ[ g'₁ ∈ (B' → B'') ] (g'₀₁ ≡ g'₁ ∘ g'₀) × (Σ[ α₁ ∈ _ ] isPushout f' g₁ g'₁ f'' α₁)
cancel-isPushoutAlong' {ℓ} {A} {B} {A'} {A'' = A''} {f = f} {g₀ = g₀} {g₁ = g₁} po₀ po₀₁ =
  pushoutRec f g₀
  {Z = λ {B' : Type ℓ} (g'₀ : B → B') (f' : A' → B') (α₀ : g'₀ ∘ f ≡ f' ∘ g₀) →
    {B'' : Type ℓ} {f'' : A'' → B''} {g'₀₁ : B → B''} {α₀₁ : g'₀₁ ∘ f ≡ f'' ∘ g₁ ∘ g₀}
     → isPushout f (g₁ ∘ g₀) g'₀₁ f'' α₀₁
     → Σ[ g'₁ ∈ (B' → B'') ] (g'₀₁ ≡ g'₁ ∘ g'₀) × (Σ[ α₁ ∈ _ ] isPushout f' g₁ g'₁ f'' α₁)}
  (λ {B'' = B''} po₀₁ →
    pushoutRec _ _
     {Z = λ {B''} g'₀₁ f'' α₀₁ →
       Σ[ g'₁ ∈ (Pushout f g₀ → B'') ] (g'₀₁ ≡ g'₁ ∘ inl) × (Σ[ α₁ ∈ _ ] isPushout inr g₁ g'₁ f'' α₁) }
     (Pushout→ _ _ _ _ (idfun _) (idfun _) g₁ refl refl , refl , _ ,
      cancel'IsPushout' {γ = refl} (funExt push) (PushoutIsPushout f g₀) (PushoutIsPushout f (g₁ ∘ g₀)) (rUnit _ ∙ rUnit _))
     _ _ _ po₀₁ )
  _ _ _ po₀ po₀₁

cancel-isPushoutAlong : {A B A' B' A'' B'' : Type ℓ} {f : A → B} {f' : A' → B'} {f'' : A'' → B''}
  {g₀ : A → A'} {g₁ : A' → A''}
  → (ipa₀ : isPushoutAlong f f' g₀) → (ipa₀₁ : isPushoutAlong f f'' (g₁ ∘ g₀))
  → Σ[ ipa₁ ∈ isPushoutAlong f' f'' g₁ ] (ipa₀₁ .fst ≡ ipa₁ .fst ∘ ipa₀ .fst)
cancel-isPushoutAlong ipa₀ ipa₀₁ with cancel-isPushoutAlong' (ipa₀ .snd .snd) (ipa₀₁ .snd .snd)
... | (g'₁ , hg' , α₁ , po) = ( g'₁ , α₁ , po ) , hg'

cancel-isPushoutAlong'' : {A B A' B' A'' B'' : Type ℓ} {f : A → B} {f' : A' → B'} {f'' : A'' → B''}
  {g₀ : A → A'} {g₁ : A' → A''} {g'₀ : B → B'} {g'₀₁ : B → B''} {α₀ : f' ∘ g₀ ≡ g'₀ ∘ f} {α₀₁ : f'' ∘ g₁ ∘ g₀ ≡ g'₀₁ ∘ f}
  → isPushout g₀ f f' g'₀ α₀ → isPushout (g₁ ∘ g₀) f f'' g'₀₁ α₀₁
  → Σ[ g'₁ ∈ (B' → B'') ] (g'₀₁ ≡ g'₁ ∘ g'₀) × (Σ[ α₁ ∈ _ ] isPushout g₁ f' f'' g'₁ α₁)
cancel-isPushoutAlong'' po₀ po₀₁ with cancel-isPushoutAlong' (transposeIsPushout po₀) (transposeIsPushout po₀₁)
... | (g'₁ , hg' , α₁ , po₁) = (g'₁ , hg' , sym α₁ , transposeIsPushout po₁)

module _ {A B A' B' A'' B'' : Type ℓ} {f : A → B} {f' : A' → B'} {f'' : A'' → B''} where
  comp-isPushoutOf : isPushoutOf f f' → isPushoutOf f' f'' → isPushoutOf f f''
  comp-isPushoutOf ipo₀ ipo₁ = ipoOfPO (paste'IsPushout (poOfIPO ipo₀) (poOfIPO ipo₁))

module _ {A B C A' B' C' : Type ℓ} {f : A → B} {f' : A' → B'} {g : B → C} {g' : B' → C'} where
  isPushoutOf-postcomp : isPushoutOf f f' → isEquiv g → isEquiv g' → isPushoutOf (g ∘ f) (g' ∘ f')
  isPushoutOf-postcomp ipo hg hg' =
    ipoOfPO (pasteIsPushout (poOfIPO ipo) (equivIsPushout' {g' = invEq e (g' ∘ ipo .snd .fst)} {α = secEq e _} hg hg'))
    where
      e = preCompEquiv (g , hg)

  isPushoutOf-precomp : isEquiv f → isEquiv f' → isPushoutOf g g' → isPushoutOf (g ∘ f) (g' ∘ f')
  isPushoutOf-precomp hf hf' ipo =
    ipoOfPO (pasteIsPushout (equivIsPushout' {g = invEq e (ipo .fst ∘ f)} {α = sym (secEq e _)} hf hf') (poOfIPO ipo))
    where
      e = postCompEquiv (f' , hf')

module _ {A B A' : Type ℓ} {f : A → B} {g : A → A'} where
  isPushoutAlongInl : isPushoutAlong g inl f
  isPushoutAlongInl .fst = inr
  isPushoutAlongInl .snd .fst = sym (funExt push)
  isPushoutAlongInl .snd .snd = transposeIsPushout (PushoutIsPushout f g)

  isPushoutOfInl : isPushoutOf {B' = Pushout f g} g inl
  isPushoutOfInl .fst = f
  isPushoutOfInl .snd = isPushoutAlongInl

  isPushoutAlongInr : isPushoutAlong f inr g
  isPushoutAlongInr .fst = inl
  isPushoutAlongInr .snd .fst = funExt push
  isPushoutAlongInr .snd .snd = PushoutIsPushout f g

  isPushoutOfInr : isPushoutOf {B' = Pushout f g} f inr
  isPushoutOfInr .fst = g
  isPushoutOfInr .snd = isPushoutAlongInr

isPushoutAlong-rec : {A B A' : Type ℓ} {f : A → B} {g : A → A'}
  (Z : {B' : Type ℓ} (f' : A' → B') → Type ℓ')
  → Z {B' = Pushout f g} inr
  → {B' : Type ℓ} (f' : A' → B') → isPushoutAlong f f' g → Z f'
isPushoutAlong-rec Z hZ f' ipa =
  pushoutRec _ _ {Z = λ g' f' α → Z f'}
  hZ (ipa .fst) f' (ipa .snd .fst) (ipa .snd .snd)

-- To prove a property about any pushout of `f`,
-- it suffices to prove it about `inr {f = f} {g = g}` for any `g`.
isPushoutOfRec : {A B : Type ℓ} {f : A → B}
  (Z : {A' B' : Type ℓ} (f' : A' → B') → Type ℓ')
  (hZ : {A' : Type ℓ} (g : A → A') → Z {B' = Pushout f g} inr)
  → {A' B' : Type ℓ} (f' : A' → B') → isPushoutOf f f' → Z f'
isPushoutOfRec Z hZ f' ipo =
  pushoutRec _ _ {Z = λ g' f' α → Z f'}
  (hZ (ipo .fst)) (ipo .snd .fst) f' (ipo .snd .snd .fst) (ipo .snd .snd .snd)

isPushoutOf→Pushout≃ : {A B A' B' : Type ℓ} {f : A → B} {f' : A' → B'}
  (ipo : isPushoutOf f f') → Pushout f (ipo .fst) ≃ B'
isPushoutOf→Pushout≃ {f = f} ipo =
  isPushoutAlong-rec (λ {B'} f' → Pushout f (ipo .fst) ≃ B') (idEquiv _) _ (ipo .snd)
