module Outline where

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.EilenbergMacLane.Base
open import Cubical.Data.Nat
open import Cubical.Data.NatMinusOne
open import Cubical.Data.Nat.Order
open import Cubical.Foundations.Everything
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.Join
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.Pushout
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp

private
  variable
    ℓ : Level

-- Generalities

join∙ : Pointed ℓ → Pointed ℓ → Pointed ℓ
join∙ ( A , a ) ( B , b ) = ( join A B , inl a )

-- Σ and Σ∙ are taken
S∙ : Pointed ℓ → Pointed ℓ
S∙ A = Susp∙ (typ A)

S∙→ : {X Y : Pointed ℓ} → (X →∙ Y) → (S∙ X →∙ S∙ Y)
S∙→ f = suspFun (fst f) , refl

S¹∙ : Pointed _
S¹∙ = ( S¹ , base )

postulate
  -- Essentially proven as EH-π in Cubical.Homotopy.Loopspace
  πGr-comm : (n : ℕ) (A : Pointed ℓ) → (a b : typ (πGr (suc n) A))
    → ·π (suc n) a b ≡ ·π (suc n) b a

-- πAb n A = πₙ₊₂(A), as an abelian group
πAb : (n : ℕ) (A : Pointed ℓ) → AbGroup ℓ
πAb n A = Group→AbGroup (πGr (1 + n) A) (πGr-comm n A)

postulate
  CofiberSeq : Pointed ℓ → Pointed ℓ → Pointed ℓ → Type ℓ
  -- CofiberSeq A B C = Σ[ f ∈ A →∙ B ] Σ[ g ∈ B →∙ C ] Σ[ h ∈ g ∘∙ f = const∙ A C ], ...
  -- Probably use a record.

  copuppe : {A B C : Pointed ℓ} → CofiberSeq A B C → CofiberSeq B C (S∙ A)

  FiberSeq : Pointed ℓ → Pointed ℓ → Pointed ℓ → Type ℓ
  -- likewise

  puppe : {X Y Z : Pointed ℓ} → FiberSeq X Y Z → FiberSeq (Ω Z) X Y

-- finitely presented abelian groups
postulate
  isFP : AbGroup ℓ → Type ℓ
  isFP-prop : {A : AbGroup ℓ} → isProp (isFP A)

-- connectivity facts
postulate
  isConnectedFunCancel : {X Y Z : Type ℓ} (f : X → Y) (g : Y → Z) (n : HLevel)
    → isConnectedFun n f → isConnectedFun (1 + n) (g ∘ f) → isConnectedFun (1 + n) g

  isConnectedFunCancel' : {X Y Z : Type ℓ} (f : X → Y) (g : Y → Z) (n : HLevel)
    → isConnectedFun (1 + n) g → isConnectedFun n (g ∘ f) → isConnectedFun n f

  -- As in 3×3 lemma for pushouts
  Pushout→ : {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Type ℓ}
    (f₁ : X₀ → X₁) (f₂ : X₀ → X₂) (g₁ : Y₀ → Y₁) (g₂ : Y₀ → Y₂)
    (h₀ : X₀ → Y₀) (h₁ : X₁ → Y₁) (h₂ : X₂ → Y₂)
    (e₁ : h₁ ∘ f₁ ≡ g₁ ∘ h₀) (e₂ : h₂ ∘ f₂ ≡ g₂ ∘ h₀)
    → Pushout f₁ f₂ → Pushout g₁ g₂

  isConnectedFunPushout : {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Type ℓ}
    (f₁ : X₀ → X₁) (f₂ : X₀ → X₂) (g₁ : Y₀ → Y₁) (g₂ : Y₀ → Y₂)
    (h₀ : X₀ → Y₀) (h₁ : X₁ → Y₁) (h₂ : X₂ → Y₂)
    (e₁ : h₁ ∘ f₁ ≡ g₁ ∘ h₀) (e₂ : h₂ ∘ f₂ ≡ g₂ ∘ h₀)
    (n : HLevel)
    → isConnectedFun n h₀ → isConnectedFun (1 + n) h₁ → isConnectedFun (1 + n) h₂
    → isConnectedFun (1 + n) (Pushout→ f₁ f₂ g₁ g₂ h₀ h₁ h₂ e₁ e₂)

  isConnectedFunJoin : {X₁ Y₁ X₂ Y₂ : Type ℓ} (f₁ : X₁ → Y₁) (f₂ : X₂ → Y₂)
    (n₁ n₂ m₁ m₂ : HLevel)
    (k : HLevel) (hk₁ : n₁ + m₂ ≤ k) (hk₂ : m₁ + n₂ ≤ k)
    → isConnectedFun n₁ f₁ → isConnectedFun n₂ f₂
    → isConnected m₁ Y₁ → isConnected m₂ Y₂
    → isConnectedFun k (join→ f₁ f₂)

  isConnectedFunS∙ : {X Y : Pointed ℓ} (f : X →∙ Y) (n : HLevel)
    → isConnectedFun n (fst f)
    → isConnectedFun n (fst (S∙→ f))

  wlp : {A B X Y : Type ℓ} (f : A → B) (g : X → Y) → Type ℓ
  -- wlp f g = ∀ (h : A → X) (k : B → Y) (e : h ∘ g ≡ k ∘ f), ∥ Σ ... ∥₁
  wlp-isProp : {A B X Y : Type ℓ} {f : A → B} {g : X → Y} → isProp (wlp f g)

  liftCell : {X Y : Type ℓ} (f : X → Y) (n : HLevel) (hf : isConnectedFun n f)
    (m : ℕ₋₁) (hm : 1+ m < n) → wlp (λ (_ : Lift (S m)) → lift tt) f

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

  isFinCW-def : {X : Type ℓ} → isFinCW X ≃ ∥ Σ[ C ∈ FinCW ℓ ] X ≡ decodeFinCW C ∥₁

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

-- stably almost finite spaces
postulate
  -- (n-1)-finite, perhaps?
  nFinite : HLevel → Type ℓ → Type ℓ
  -- nFinite {ℓ} n X = ∥ Σ[ C ∈ FinCW ℓ ] Σ[ f ∈ (decodeFinCW C → X) ] isConnectedFun n f ∥₁
  nFinite-isProp : {n : HLevel} {X : Type ℓ} → isProp (nFinite n X)

  stablyNFinite : HLevel → Pointed ℓ → Type ℓ
  stablyNFinite-isProp : {n : HLevel} {X : Pointed ℓ} → isProp (stablyNFinite n X)

  saf : Pointed ℓ → Type ℓ
  saf-isProp : {X : Pointed ℓ} → isProp (saf X)

  isFinCW→saf : {X : Pointed ℓ} → isFinCW (typ X) → saf X

  stablyNFiniteOfSusp : (n : HLevel) (A : Pointed ℓ)
    → stablyNFinite (suc n) (S∙ A) → stablyNFinite n A

  stablyNFiniteExtension : {n : HLevel} {A B C : Pointed ℓ} (S : CofiberSeq A B C)
    → stablyNFinite n A → stablyNFinite n C → stablyNFinite n B

  safCofiber : {A B C : Pointed ℓ} → CofiberSeq A B C
    → saf A → saf B → saf C

  safExtension : {A B C : Pointed ℓ} → CofiberSeq A B C
    → saf A → saf C → saf B

  safS¹× : {A : Pointed ℓ} → saf A → saf (S¹∙ ×∙ A)

  -- TODO: Most likely the inequalities on `k` are not quite right
  stablyNFiniteJoin : {X₁ X₂ : Pointed ℓ} (m₁ n₁ m₂ n₂ : HLevel)
    (hXm₁ : isConnected m₁ (typ X₁)) (hXn₁ : stablyNFinite n₁ X₁)
      (hXm₂ : isConnected m₂ (typ X₂)) (hXn₂ : stablyNFinite n₂ X₂)
    (k : HLevel) (hk₁ : n₁ + m₂ ≤ k) (hk₂ : m₁ + n₂ ≤ k)
    → stablyNFinite k (join∙ X₁ X₂)

  stablyNFiniteApprox : {X Y : Pointed ℓ} (f : X →∙ Y)
    (n : HLevel) (hf : isConnectedFun n (fst f))
    → stablyNFinite (1 + n) X → stablyNFinite n Y

  stablyNFiniteApprox' : {X Y : Pointed ℓ} (f : X →∙ Y)
    (n : HLevel) (hf : isConnectedFun n (fst f))
    → stablyNFinite n Y → stablyNFinite n X

postulate
  -- Bottom homotopy groups, e.g.,
  -- if n = 0 we are talking about π₂(X),
  -- and X must be simply connected = 1-connected.
  isFinCW→isFPBottomπ : (X : Pointed ℓ) (hX : isFinCW (typ X))
    (n : ℕ) (cX : isConnected (3 + n) (typ X))
    → isFP (πAb n X)

  -- Could weaken hypothesis to stablyNFinite n X (or so).
  saf→isFPBottomπ : (X : Pointed ℓ) (hX : saf X)
    (n : ℕ) (cX : isConnected (3 + n) (typ X))
    → isFP (πAb n X)

  saf→Conn→isFPπ : (X : Pointed ℓ) (hX : saf X)
    (n : ℕ) (cX : isConnected (suc (suc n)) (typ X))
    → isFP (πAb n X)

postulate
  safΩ→saf : {B : Pointed ℓ} (cB : isConnected 2 (typ B)) → saf (Ω B) → saf B
  saf→safΩ : {B : Pointed ℓ} (scB : isConnected 3 (typ B)) → saf B → saf (Ω B)
  safTotal : {F E B : Pointed ℓ} (S : FiberSeq F E B) (scB : isConnected 3 (typ B))
    → saf B → saf F → saf E

postulate
  isFP→safEM : (A : AbGroup ℓ) (fpA : isFP A) (n : ℕ)
    → saf (EM∙ A (suc n))

postulate
  -- n+1 connected cover
  _⦉_⦊ : (X : Pointed ℓ) → ℕ → Pointed ℓ
  1ConnCovEq : (X : Pointed ℓ) (scX : isConnected 3 (typ X))
    → X ≡ (X ⦉ 0 ⦊)
  Conn→ConnConnCov : (X : Pointed ℓ) (m n : ℕ)
    → isConnected m (typ X) → isConnected m (typ (X ⦉ n ⦊))
  ConnCovIsConn : (X : Pointed ℓ) (n : ℕ)
    → isConnected (3 + n) (typ (X ⦉ n ⦊))
  πConnCov : (X : Pointed ℓ) (n k : ℕ) → k ≥ n
    → (πAb (suc k) (X ⦉ n ⦊)) ≡ (πAb (suc k) X)
  ⦉-⦊EMFibSeq : (X : Pointed ℓ) (n : ℕ)
    → FiberSeq (EM∙ (πAb n X) (suc n)) (X ⦉ (suc n) ⦊) (X ⦉ n ⦊)

postulate
  saf→isFPπ : (X : Pointed ℓ) (safX : saf X) (scX : isConnected 3 (typ X)) (n : ℕ)
    → isFP (πAb n X)
  saf→saf⦉-⦊ : (X : Pointed ℓ) (safX : saf X) (scX : isConnected 3 (typ X)) (n : ℕ)
    → saf (X ⦉ n ⦊)
   
