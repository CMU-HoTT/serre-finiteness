module Pushout.Fold where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.HITs.Pushout

open import Pushout.IsPushout

private
  variable
    ℓ ℓ' ℓ'' : Level

fold : {X Y : Type ℓ} (f : X → Y) → (Pushout f f → Y)
fold f (inl y) = y
fold f (inr y) = y
fold f (push x i) = f x

isEquiv-fold-id : {X : Type ℓ} → isEquiv (fold (idfun X))
isEquiv-fold-id {X = X} = isoToIsEquiv i
  where
    open Iso
    i : Iso (Pushout (idfun X) (idfun X)) X
    i .fun = fold (idfun X)
    i .inv = inl
    i .rightInv b =  refl
    i .leftInv (inl b) = refl
    i .leftInv (inr b) = push b
    i .leftInv (push b i) = λ j → push b (i ∧ j)

module FoldStuff where
  changeApex : {A B X Y : Type ℓ} (f : A → B) (g : B → X) (h : B → Y)
    → Pushout (g ∘ f) (h ∘ f) → Pushout g h
  changeApex f g h (inl x) = inl x
  changeApex f g h (inr y) = inr y
  changeApex f g h (push a i) = push (f a) i

  -- Functoriality of pushout in first argument, i.e., of - ⊔_A Y
  Pushout→₁ : {A X Y X' : Type ℓ} (g : A → X) (h : A → Y) (k : X → X')
    → Pushout g h → Pushout (k ∘ g) h
  Pushout→₁ g h k (inl x) = inl (k x)
  Pushout→₁ g h k (inr y) = inr y
  Pushout→₁ g h k (push a i) = push a i

  -- Functoriality of pushout in second argument, i.e., of X ⊔_A -
  Pushout→₂ : {A X Y Y' : Type ℓ} (g : A → X) (h : A → Y) (k : Y → Y')
    → Pushout g h → Pushout g (k ∘ h)
  Pushout→₂ g h k (inl x) = inl x
  Pushout→₂ g h k (inr y) = inr (k y)
  Pushout→₂ g h k (push a i) = push a i

  module _ {A X Y Y' : Type ℓ} (g : A → X) (h : A → Y) (k : Y → Y') where
    po1 : isPushout inr k (Pushout→₂ g h k) inr refl
    po1 = cancel'IsPushout' _ (PushoutIsPushout g h) (PushoutIsPushout g (k ∘ h)) (rUnit _)

  module _ {A B X Y Y' : Type ℓ} (f : A → B) (g : B → X) (h : B → Y) (k : Y → Y') where
    sqα : Pushout→₂ g h k ∘ changeApex f g h ≡ changeApex f g (k ∘ h) ∘ Pushout→₂ (g ∘ f) (h ∘ f) k
    -- refl after cases on argument
    sqα j (inl x) = inl x
    sqα j (inr y) = inr (k y)
    sqα j (push a i) = push (f a) i

    po : isPushout (changeApex f g h) (Pushout→₂ (g ∘ f) (h ∘ f) k) (Pushout→₂ g h k) (changeApex f g (k ∘ h)) sqα
    po = cancelIsPushout' _ (po1 (g ∘ f) (h ∘ f) k) (po1 g h k) (rUnit _)

  module _ {A X Y X' : Type ℓ} (g : A → X) (h : A → Y) (k : X → X') where
    po1' : isPushout inl k (Pushout→₁ g h k) inl refl
    po1' = cancel'IsPushout' _
      (transposeIsPushout (PushoutIsPushout g h)) (transposeIsPushout (PushoutIsPushout (k ∘ g) h)) (rUnit _)

  module _ {A B X Y X' : Type ℓ} (f : A → B) (g : B → X) (h : B → Y) (k : X → X') where
    sqα' : Pushout→₁ g h k ∘ changeApex f g h ≡ changeApex f (k ∘ g) h ∘ Pushout→₁ (g ∘ f) (h ∘ f) k
    -- refl after cases on argument
    sqα' j (inl x) = inl (k x)
    sqα' j (inr y) = inr y
    sqα' j (push a i) = push (f a) i

    po' : isPushout (changeApex f g h) (Pushout→₁ (g ∘ f) (h ∘ f) k) (Pushout→₁ g h k) (changeApex f (k ∘ g) h) sqα'
    po' = cancelIsPushout' _ (po1' (g ∘ f) (h ∘ f) k) (po1' g h k) (lUnit _)

  module _ {A B X Y : Type ℓ} (f : A → B) (g : B → X) (h : X → Y) where
    po2 : isPushout (changeApex f g g) _ _ (changeApex f (h ∘ g) (h ∘ g)) _
    po2 = paste'IsPushout (po f g g h) (po' f g (h ∘ g) h)

    ipo2 : isPushoutOf (changeApex f g g) (changeApex f (h ∘ g) (h ∘ g))
    ipo2 = ipoOfPO po2

  module _ {A B C : Type ℓ} (f : A → B) (g : B → C) where
    private
      lem : fold (idfun B) ∘ changeApex f (idfun B) (idfun B) ≡ fold f
      lem i (inl b) = b
      lem i (inr b) = b
      lem i (push a j) = f a

    po3 : isPushoutOf (fold f) (changeApex f g g)
    po3 =
      subst (λ F → isPushoutOf F (changeApex f g g)) lem
        (isPushoutOf-postcomp (ipo2 f (idfun B) g) isEquiv-fold-id (idIsEquiv _))

  module _ {A B A' B' : Type ℓ} {f : A → B} {f' : A' → B'} (gA : A → A') (gB : B → B') (α : gB ∘ f ≡ f' ∘ gA)
    (po : isPushout f gA gB f' α) where
    P : Type ℓ
    P = Pushout f f

    P' : Type ℓ
    P' = Pushout f' f'

    gP : P → P'
    gP = Pushout→ f f f' f' gA gB gB α α

    inlB' : B' → P'
    inlB' = inl

    σ : (p : P) → gB (fold f p) ≡ fold f' (gP p)
    σ (inl b) = refl
    σ (inr b) = refl
    σ (push a i) = λ j → w (~ j) i
      where
        w : cong (fold f' ∘ gP) (push a) ≡ refl {x = gB (f a)}
        w = cong-∙∙ (fold f') (λ j → inl (α j a)) (push (gA a)) (λ j → inr (α (~ j) a)) ∙ ∙∙lCancel (sym (α ≡$ a))

    γ : (b : B) → gB (fold f (inr b)) ≡ fold f' (inr (gB b))
    γ b = σ (inl b) ∙ refl

    γ≡ : (b : B) → γ b ≡ refl
    γ≡ b = sym compPathRefl

    po4 : isPushout inr gB gP inr refl
    po4 = cancel'IsPushout' _ (PushoutIsPushout f f) (pasteIsPushout po6 po12) (λ j i a → e' a j i)
      where
        po6 : isPushout (idfun A) (gB ∘ f) (f' ∘ gA) (idfun B') (sym α)
        po6 = equivIsPushout' (idIsEquiv _) (idIsEquiv _)

        po12 : isPushout f (f' ∘ gA) (inl ∘ gB) inr _
        po12 = paste'IsPushout po (PushoutIsPushout f' f')

        e' : (a : A) → (cong inlB' (α ≡$ a) ∙ push (gA a)) ∙ cong inr (sym (α ≡$ a)) ≡ (cong gP (push a) ∙ refl)
        e' a = sym (doubleCompPath-elim _ _ _) ∙ rUnit _

    po7 : isPushout (fold f) gP gB (fold f') (funExt σ)
    po7 = cancelIsPushout po4 (equivIsPushout' (idIsEquiv _) (idIsEquiv _))

    ipo : isPushoutOf (fold f) (fold f')
    ipo .fst = gP
    ipo .snd .fst = gB
    ipo .snd .snd .fst = (funExt σ)
    ipo .snd .snd .snd = po7

open FoldStuff

task1 : {A B A' B' : Type ℓ} {f : A → B} {f' : A' → B'} (h : isPushoutOf f f') →
  isPushoutOf (fold f) (fold f')
task1 h = ipo (h .fst) (h .snd .fst) (h .snd .snd .fst) (h .snd .snd .snd)

task2 : {A B C : Type ℓ} (f : A → B) (g : B → C) →
  Σ[ h ∈ (Pushout (g ∘ f) (g ∘ f) → Pushout g g) ]
  (fold (g ∘ f) ≡ fold g ∘ h) × isPushoutOf (fold f) h
task2 f g .fst = changeApex f g g
task2 f g .snd .fst i (inl c) = c
task2 f g .snd .fst i (inr c) = c
task2 f g .snd .fst i (push a j) = g (f a)
task2 f g .snd .snd = po3 f g
