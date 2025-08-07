module FiniteCW where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Fin.Inductive

open import Cubical.HITs.Join
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Truncation as TR

open import Cubical.Homotopy.Connected

open import Cubical.CW.Base
open import Cubical.CW.Subcomplex
open import Cubical.CW.Instances.Pushout renaming (isFinCWPushout to isFinCWPushout')
open import Cubical.CW.Instances.Unit
open import Cubical.CW.Instances.Empty
open import Cubical.CW.Instances.Sigma
open import Cubical.CW.Instances.Sn
open import Cubical.CW.Instances.Susp renaming (isFinCWSusp to isFinCWSusp')
open import Cubical.CW.Instances.Join renaming (isFinCWJoin to isFinCWJoin')
open import Cubical.CW.Properties

open import Cubical.Axiom.Choice

private
  variable
    ℓ : Level

-- todo: is this needed?
Susp^∙ : ℕ → Pointed ℓ → Pointed ℓ
Susp^∙ n x .fst = Susp^ n (typ x)
Susp^∙ zero x .snd = pt x
Susp^∙ (suc n) x .snd = Susp^∙ n (Susp∙ (typ x)) .snd

Susp^Fun : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B)
  (n : ℕ) → Susp^ n A → Susp^ n B
Susp^Fun f zero = f
Susp^Fun f (suc n) = Susp^Fun (suspFun f) n

Susp^Fun∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B)
  (n : ℕ) → Susp^∙ n A →∙ Susp^∙ n B
fst (Susp^Fun∙ f n) = Susp^Fun (fst f) n
snd (Susp^Fun∙ f zero) = snd f
snd (Susp^Fun∙ f (suc n)) = Susp^Fun∙ (suspFun∙ (fst f)) n .snd

Susp^Equiv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A ≃ B)
  (n : ℕ) → Susp^ n A ≃ Susp^ n B
Susp^Equiv f n .fst = Susp^Fun (fst f) n
Susp^Equiv f zero .snd = snd f
Susp^Equiv f (suc n) .snd =
  Susp^Equiv (isoToEquiv (congSuspIso (equivToIso f))) n .snd

Susp^Equiv∙ : {A B : Pointed ℓ} (n : ℕ)
  → A ≃∙ B →  Susp^∙ n A ≃∙ Susp^∙ n B
Susp^Equiv∙ n e .fst = Susp^Equiv (fst e) n
Susp^Equiv∙ n e .snd = Susp^Fun∙ (≃∙map e) n .snd

Susp^-comm-Iso : (n : ℕ) (X : Type ℓ)
  → Iso (Susp^ (1 + n) X) (Susp (Susp^ n X))
Susp^-comm-Iso zero X = idIso
Susp^-comm-Iso (suc n) X = Susp^-comm-Iso n (Susp X)

Susp^-comm-Equiv∙ : (n : ℕ) (X : Pointed ℓ)
  → (Susp^∙ (1 + n) X) ≃∙ (Susp∙ (Susp^ n (typ X)))
Susp^-comm-Equiv∙ n X .fst = isoToEquiv (Susp^-comm-Iso n (typ X))
Susp^-comm-Equiv∙ zero X .snd = refl
Susp^-comm-Equiv∙ (suc n) X .snd =
  Susp^-comm-Equiv∙ n (Susp∙ (typ X)) .snd

Susp^-comm : (n : ℕ) (X : Type ℓ) → Susp^ (1 + n) X
                                   ≡ Susp (Susp^ n X)
Susp^-comm zero X = refl
Susp^-comm (suc n) X = Susp^-comm n (Susp X)

Susp^-conn : (m n : ℕ) (X : Type ℓ) → isConnected m X
             → isConnected (n + m) (Susp^ n X)
Susp^-conn m zero X hX = hX
Susp^-conn m (suc n) X hX =
  transport (λ i → isConnected (+-suc n m i) (Susp^ (suc n) X))
             (Susp^-conn (suc m) n (Susp X) (isConnectedSusp m hX))

  -- The type of "finite CW complex structures".
  -- We need to expose this separately from `isFinCW`
  -- if we want to define e.g. `nFinite n X` as a *small* proposition.
  -- (Possibly we don't really care.)
FinCW : (ℓ : Level) → Type (ℓ-suc ℓ)
FinCW = finCW

decodeFinCW : finCW ℓ → Type ℓ
decodeFinCW = fst

isFinCW-isProp : {X : Type ℓ} → isProp (isFinCW X)
isFinCW-isProp = squash₁

isFinCW-def : {X : Type ℓ} → isFinCW X ≃ (∥ (Σ[ C ∈ FinCW ℓ ] (X ≡ decodeFinCW C)) ∥₁)
isFinCW-def {ℓ = ℓ} {X = X} = propBiimpl→Equiv squash₁ squash₁
  (PT.map (λ A → (X , ∣ A ∣₁) , refl))
  (PT.rec squash₁ (uncurry (uncurry λ X' A p → help X' A X (sym p))))
  where
  help : (x : Type ℓ) (y : isFinCW x)
      (X : Type ℓ)
      (y₁ : decodeFinCW (x , y) ≡ X) →
      isFinCW X
  help X A = J> A

isFinCW-def-fun : {X : Type ℓ} → isFinCW X → (∥ (Σ[ C ∈ FinCW ℓ ] X ≡ decodeFinCW C) ∥₁)
isFinCW-def-fun = fst isFinCW-def

hasNDimFinCW : ℕ → Type ℓ → Type (ℓ-suc ℓ)
hasNDimFinCW {ℓ = ℓ} n X = Σ[ X' ∈ finCWskel ℓ n ] X ≃ realise (finCWskel→CWskel n X')

-- `isNDimFinCW n X` = "X is a finite (n-1)-dimensional CW complex".
isNDimFinCW : ℕ → Type ℓ → Type (ℓ-suc ℓ)
isNDimFinCW n X = ∥ hasNDimFinCW n X ∥₁

isNDimFinCW-isProp : {n : ℕ} {X : Type ℓ} → isProp (isNDimFinCW n X)
isNDimFinCW-isProp = squash₁

isNDimFinCW→isFinCW : {n : ℕ} {X : Type ℓ} → isNDimFinCW n X
                                            → isFinCW X
isNDimFinCW→isFinCW {n = n} = PT.map λ c → n , c

isFinCWUnit : isFinCW (Unit* {ℓ = ℓ})
isFinCWUnit = finCWUnit* _ .snd

isFinCWSn : {n : ℕ} → isFinCW (S₊ n)
isFinCWSn {n = n} = Sᶠⁱⁿᶜʷ n .snd

isFinCWSusp : {n : ℕ} (X : Type ℓ) → isFinCW X → isFinCW (Susp^ n X)
isFinCWSusp {n = zero} X cw = cw
isFinCWSusp {ℓ = ℓ}{n = suc n} X cw =
  isFinCWSusp {n = n} (Susp X)
    (subst isFinCW PushoutSusp≡Susp
      (subst isFinCW (ua
        (pushoutEquiv _ _ _ _
          (idEquiv _) (invEquiv Unit≃Unit*) (invEquiv Unit≃Unit*)
            refl refl))
        (isFinCWPushout' (_ , cw) (finCWUnit* ℓ) (finCWUnit* ℓ)
          (λ _ → tt*) λ _ → tt*)))

isFinCWPushout : {X Y Z : Type ℓ} (f : X → Y) (g : X → Z)
  → isFinCW X → isFinCW Y → isFinCW Z → isFinCW (Pushout f g)
isFinCWPushout f g cwX cwY cwZ =
  isFinCWPushout' (_ , cwX) (_ , cwY) (_ , cwZ) f g

isFinCWJoin : {X Y : Type ℓ} → isFinCW X → isFinCW Y → isFinCW (join X Y)
isFinCWJoin cwX cwY = isFinCWJoin' (_ , cwX) (_ , cwY)

preLiftFromNDimFinCW : {Y Z : Type ℓ} (n : ℕ) (X : CWskel ℓ)
  → (f : Y → Z)
  → isConnectedFun n f
  → (g : fst X n → Z)
  → ∃[ l ∈ (fst X n → Y) ] (f ∘ l ≡ g)
preLiftFromNDimFinCW zero X f isc g =
  ∣ (λ x → ⊥.rec (X .snd .snd .snd .fst x))
    , (funExt (λ x → ⊥.rec (X .snd .snd .snd .fst x))) ∣₁
preLiftFromNDimFinCW {Y = Y} {Z} (suc n) X f isc =
  subst (λ X → (g : X → Z) → ∃[ l ∈ (X → Y) ] (f ∘ l ≡ g))
        (ua (invEquiv (X .snd .snd .snd .snd n)))
        (λ g → PT.rec squash₁ (uncurry (main g))
          (preLiftFromNDimFinCW n X f (isConnectedFunSubtr n 1 f isc) (g ∘ inl)))
  where
  α = X .snd .snd .fst n
  Xₙ₊₁ = Pushout α fst

  module _ (g : Xₙ₊₁ → Z) (l : fst X n → Y) (lcomm : f ∘ l ≡ g ∘ inl) where
    P : Xₙ₊₁ → Type _
    P x = fiber f (g x)

    lem : (n' : ℕ) → n ≡ n' → (x : Fin (fst (X .snd) n))
      → ∃[ s ∈ P (inr x) ]
           (∥ (((t : S⁻ n)
           → s ≡ ((l (α (x , t))) , (funExt⁻ lcomm (α (x , t)) ∙ cong g (push (x , t)))))) ∥₁)
    lem zero p x = TR.rec squash₁
      (λ a → ∣ a , ∣ (λ x → ⊥.rec (subst S⁻ p x)) ∣₁ ∣₁)
      (subst (λ n → isConnectedFun (suc n) f) p isc
             (g (inr x)) .fst)
    lem (suc n') p x =
      PT.map (λ F → (F ⋆S i0) , ∣ F ∣₁)
      (sphereToTrunc n {A = λ t →
      Path (P (inr x))
            (l (α (x , ⋆S)) , (funExt⁻ lcomm (α (x , ⋆S)) ∙ cong g (push (x , ⋆S))))
            ((l (α (x , t))) , (funExt⁻ lcomm (α (x , t)) ∙ cong g (push (x , t)))) }
           λ x → isConnectedPath n (isc _) _ _ .fst)
      where
      ⋆S : S⁻ n
      ⋆S = subst S⁻ (sym p) (ptSn n')

    lemImproved : (x : Fin (fst (X .snd) n))
      → hLevelTrunc 1 (Σ[ s ∈ P (inr x) ]
           ((((t : S⁻ n)
           → s ≡ ((l (α (x , t))) , (funExt⁻ lcomm (α (x , t)) ∙ cong g (push (x , t))))))))
    lemImproved x = PT.rec (isOfHLevelTrunc 1)
      (uncurry (λ pinr → PT.rec (isOfHLevelTrunc 1)
                                 (λ w → ∣ pinr , w ∣ₕ)))
      (lem n refl x)

    main : ∃[ l ∈ (Xₙ₊₁ → Y) ] (f ∘ l ≡ g)
    main = TR.rec squash₁ (λ F
      → ∣ (λ { (inl x) → l x
              ; (inr x) → F x .fst .fst -- F x .fst .fst
              ; (push (x , a) i) → F x .snd a (~ i) .fst})
            , funExt (λ { (inl x) → funExt⁻ lcomm x
                        ; (inr x) → F x .fst .snd
                        ; (push (x , a) i) j
                          → hcomp (λ k → λ {(i = i0) → compPath-filler
                                                          (funExt⁻ lcomm (α (x , a)))
                                                          (cong g (push (x , a))) (~ k) j
                                           ; (i = i1) → F x .fst .snd j
                                           ; (j = i0) → f (F x .snd a (~ i) .fst)
                                           ; (j = i1) → g (push (x , a) (i ∨ ~ k))})
                                  (F x .snd a (~ i) .snd j)})∣₁)
           (invEq (_ , InductiveFinSatAC 1 (fst (X .snd) n) _) lemImproved)

liftFromNDimFinCW : (n : ℕ) (X : Type ℓ) (hX : isNDimFinCW n X)
  {Y Z : Type ℓ} (f : Y → Z) (hf : isConnectedFun n f) (g : X → Z)
  → ∃[ l ∈ (X → Y) ] (f ∘ l ≡ g)
liftFromNDimFinCW n X hX {Y} {Z} f =
  PT.rec (isPropΠ2 (λ _ _ → squash₁))
    (λ Xstr cf
     → subst (λ X → (g : X → Z) → ∃-syntax (X → Y) (λ l → f ∘ l ≡ g))
              (ua (compEquiv (isoToEquiv (realiseFin n (Xstr .fst))) (invEquiv (Xstr .snd))))
              (preLiftFromNDimFinCW n
                (Xstr .fst .fst , Xstr .fst .snd .fst) f cf)) hX

-- A finite CW complex admits an (n-2)-connected map from an (n-1)-dimensional finite CW complex.
mapFromNSkel : (X : Type ℓ) (hX : isFinCW X) (n : ℕ)
  → ∃[ Y ∈ Type ℓ ] Σ[ hY ∈ isNDimFinCW n Y ] Σ[ f ∈ (Y → X) ] isConnectedFun n f
mapFromNSkel X = PT.rec (isPropΠ (λ _ → squash₁))
  λ {(dim , sk , e) n → ∣ fst sk n
                       , ∣ (subComplex (finCWskel→CWskel dim sk) n .fst
                         , (subComplexYieldsFinCWskel (finCWskel→CWskel dim sk) n))
                       , isoToEquiv (realiseSubComplex n (finCWskel→CWskel dim sk)) ∣₁
                       , subst (λ X → Σ (sk .fst n → X) (isConnectedFun n))
                               (ua (invEquiv e))
                               ((CW↪∞ (finCWskel→CWskel dim sk) n)
                              , isConnected-CW↪∞ n (finCWskel→CWskel dim sk)) ∣₁}
