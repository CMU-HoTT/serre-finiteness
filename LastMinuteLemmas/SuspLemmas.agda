module LastMinuteLemmas.SuspLemmas where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat

open import Cubical.HITs.Pushout
open import Cubical.HITs.Wedge
open import Cubical.HITs.Susp



open import FiniteCW


private
  variable
    ℓ : Level


-- Move to Cubical.HITs.Susp.Properties
module _ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
         {f : A → B} {g : A → C} where
  private
    F : (a : A) (i j k : I) → Pushout (suspFun f) (suspFun g)
    F a i j k = hfill (λ k →
      λ{(i = i0) → inl (merid (f a) j)
      ; (i = i1) → doubleCompPath-filler (push north)
                      (λ i → inr (merid (g a) i))
                      (sym (push south)) k j
      ; (j = i0) → push north (~ k ∧ i)
      ; (j = i1) → push south (~ k ∧ i)})
            (inS (push (merid a j) i)) k

  SuspPushout→PushoutSusp : Susp (Pushout f g) → Pushout (suspFun f) (suspFun g)
  SuspPushout→PushoutSusp north = inl north
  SuspPushout→PushoutSusp south = inl south
  SuspPushout→PushoutSusp (merid (inl x) i) = inl (merid x i)
  SuspPushout→PushoutSusp (merid (inr x) i) =
    (push north ∙∙ (λ i → inr (merid x i)) ∙∙ sym (push south)) i
  SuspPushout→PushoutSusp (merid (push a i) j) = F a i j i1

  PushoutSusp→SuspPushout : Pushout (suspFun f) (suspFun g) → Susp (Pushout f g)
  PushoutSusp→SuspPushout (inl x) = suspFun inl x
  PushoutSusp→SuspPushout (inr x) = suspFun inr x
  PushoutSusp→SuspPushout (push north i) = north
  PushoutSusp→SuspPushout (push south i) = south
  PushoutSusp→SuspPushout (push (merid a i) j) = merid (push a j) i

  SuspCommPushoutIso : Iso (Susp (Pushout f g))
                           (Pushout (suspFun f) (suspFun g))
  SuspCommPushoutIso .Iso.fun = SuspPushout→PushoutSusp
  SuspCommPushoutIso .Iso.inv = PushoutSusp→SuspPushout
  SuspCommPushoutIso .Iso.rightInv (inl north) = refl
  SuspCommPushoutIso .Iso.rightInv (inl south) = refl
  SuspCommPushoutIso .Iso.rightInv (inl (merid a i)) = refl
  SuspCommPushoutIso .Iso.rightInv (inr north) = push north
  SuspCommPushoutIso .Iso.rightInv (inr south) = push south
  SuspCommPushoutIso .Iso.rightInv (inr (merid a i)) j =
    doubleCompPath-filler (push north)
                          (λ i → inr (merid a i))
                          (sym (push south)) (~ j) i
  SuspCommPushoutIso .Iso.rightInv (push north i) j = push north (i ∧ j)
  SuspCommPushoutIso .Iso.rightInv (push south i) j = push south (i ∧ j)
  SuspCommPushoutIso .Iso.rightInv (push (merid a i) j) k =
    hcomp (λ r →
      λ{(i = i0) → push north ((k ∨ ~ r) ∧ j)
      ; (i = i1) → push south ((k ∨ ~ r) ∧ j)
      ; (j = i0) → inl (merid (f a) i)
      ; (j = i1) → doubleCompPath-filler (push north)
                      (λ i → inr (merid (g a) i))
                      (sym (push south)) (~ k ∧ r) i
      ; (k = i1) → push (merid a i) j})
      (push (merid a i) j)
  SuspCommPushoutIso .Iso.leftInv north = refl
  SuspCommPushoutIso .Iso.leftInv south = refl
  SuspCommPushoutIso .Iso.leftInv (merid (inl x) i) = refl
  SuspCommPushoutIso .Iso.leftInv (merid (inr x) i) j =
    PushoutSusp→SuspPushout
      (doubleCompPath-filler (push north)
                          (λ i → inr (merid x i))
                          (sym (push south)) (~ j) i)
  SuspCommPushoutIso .Iso.leftInv (merid (push a j) i) k =
    hcomp (λ r →
      λ{(i = i0) → north
      ; (i = i1) → south
      ; (j = i0) → merid (inl (f a)) i
      ; (j = i1) → PushoutSusp→SuspPushout
                   (doubleCompPath-filler (push north)
                          (λ i → inr (merid (g a) i))
                          (sym (push south)) (~ k ∧ r) i)
      ; (k = i0) → PushoutSusp→SuspPushout (F a j i r)
      ; (k = i1) → merid (push a j) i})
      (merid (push a j) i)

-- Move to Cubical.HITs.Susp.Properties
Iso-SuspUnit-Unit : Iso (Susp Unit) Unit
Iso-SuspUnit-Unit .Iso.fun x = tt
Iso-SuspUnit-Unit .Iso.inv x = north
Iso-SuspUnit-Unit .Iso.rightInv tt = refl
Iso-SuspUnit-Unit .Iso.leftInv north = refl
Iso-SuspUnit-Unit .Iso.leftInv south = merid tt
Iso-SuspUnit-Unit .Iso.leftInv (merid a i) j = merid tt (i ∧ j)

-- Move to Cubical.HITs.Wedge.Properties
⋁Iso : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Pointed ℓ} {B : Pointed ℓ'}
  {C : Pointed ℓ''} {D : Pointed ℓ'''} (e : A ≃∙ C) (e' : B ≃∙ D)
  → Iso (A ⋁ B) (C ⋁ D)
⋁Iso e e' = pushoutIso _ _ _ _
  (idEquiv Unit) (fst e) (fst e')
    (funExt (λ x → snd e))
    (funExt (λ x → snd e'))

Iso-⋁Susp-Susp⋁ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
  → Iso (Susp (A ⋁ B)) (Susp∙ (typ A) ⋁ Susp∙ (typ B))
Iso-⋁Susp-Susp⋁ {A = A} {B} =
  compIso SuspCommPushoutIso
    (pushoutIso _ _ _ _
      (isoToEquiv Iso-SuspUnit-Unit) (idEquiv _) (idEquiv _)
      (funExt (λ { north → refl ; south → sym (merid (pt A))
                ; (merid a i) j → merid (pt A) (~ j ∧ i)}))
      (funExt (λ { north → refl ; south → sym (merid (pt B))
                ; (merid a i) j → merid (pt B) (~ j ∧ i)})))

⋁Susp≃∙Susp⋁ : (X Y : Pointed ℓ)
  → Susp∙ (X ⋁ Y) ≃∙ (Susp∙ (typ X) ⋁∙ₗ Susp∙ (typ Y))
⋁Susp≃∙Susp⋁ X Y .fst = isoToEquiv Iso-⋁Susp-Susp⋁
⋁Susp≃∙Susp⋁ X Y .snd = refl

⋁Susp^≃∙Susp^⋁ : (X Y : Pointed ℓ) (n : ℕ)
  → Susp^∙ n (X ⋁∙ₗ Y) ≃∙ (Susp^∙ n X ⋁∙ₗ Susp^∙ n Y)
⋁Susp^≃∙Susp^⋁ X Y zero = idEquiv∙ _
⋁Susp^≃∙Susp^⋁ X Y (suc n) =
  compEquiv∙ (Susp^Equiv∙ n (⋁Susp≃∙Susp⋁ X Y))
             (⋁Susp^≃∙Susp^⋁ (Susp∙ (typ X)) (Susp∙ (typ Y)) n)
