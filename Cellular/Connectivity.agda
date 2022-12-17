module Cellular.Connectivity where

import Cubical.Data.Empty as Empty
open import Cubical.Data.Fin
open import Cubical.Data.FinData.Base renaming (Fin to FinData) hiding (¬Fin0 ; toℕ)
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Nat.Order
open import Cubical.Data.NatMinusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (rec) renaming (map to map⊎)
open import Cubical.Data.Unit
open import Cubical.Foundations.Everything
open import Cubical.Functions.Surjection
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation using (propTruncTrunc1Iso)
open import Cubical.Homotopy.Connected

open import Cellular.EmptyFamily using (rec') -- TODO move
open import Cellular.Recombination
open import Cellular.RelativeCellComplex
open import Pushout.Fold
open import Pushout.IsPushout

private
  variable
    ℓi ℓ ℓ' : Level

open Family

-- TODO[cubical]: move
isPropIsConnectedFun : {X : Type ℓ} {Y : Type ℓ'} {f : X → Y} {n : ℕ}
  → isProp (isConnectedFun n f)
isPropIsConnectedFun = isPropΠ λ _ → isPropIsContr

isConnectedId : {X : Type ℓ} (n : ℕ) → isConnectedFun n (idfun X)
isConnectedId = isEquiv→isConnected (idfun _) (idIsEquiv _)

module _ (ℐ : Family {ℓi = ℓi} {ℓ = ℓ}) where
  FamilyConnected : ℕ → Type _
  FamilyConnected n =
    (i : Ix ℐ) → isConnectedFun n (j ℐ i)

  module _ {n : ℕ} (fc : FamilyConnected n) where
    conn-isRCC : {X Y : Type ℓ} {f : X → Y}
      → isRelativeCellComplex ℐ f
      → isConnectedFun n f
    conn-isRCC =
      isRCCElimProp ℐ (isConnectedFun n) (λ f → isPropIsConnectedFun)
      (isConnectedId n) (λ f g hf hg → isConnectedComp g f n hg hf) (fc _)
      (inrConnected n) _

isConnectedPushout : {X Y X' Y' : Type ℓ} {f : X → Y} {f' : X' → Y'} (n : ℕ)
  → isPushoutOf f f' → isConnectedFun n f → isConnectedFun n f'
isConnectedPushout n ipo hf =
  isPushoutOfRec (λ f' → isConnectedFun n f') (λ g → inrConnected n _ _ hf) _ ipo

-- TODO[cubical]: move

private
  -- Copied from Cubical.Homotopy.Connected
  typeToFiberIso : ∀ {ℓ} (A : Type ℓ) → Iso A (fiber (λ (x : A) → tt) tt)
  Iso.fun (typeToFiberIso A) x = x , refl
  Iso.inv (typeToFiberIso A) = fst
  Iso.rightInv (typeToFiberIso A) b i = fst b , (isOfHLevelSuc 1 (isPropUnit) tt tt (snd b) refl) i
  Iso.leftInv (typeToFiberIso A) a = refl

  typeToFiber : ∀ {ℓ} (A : Type ℓ) → A ≡ fiber (λ (x : A) → tt) tt
  typeToFiber A = isoToPath (typeToFiberIso A)

isConnectedFun→isConnected : {X : Type ℓ} (n : ℕ)
  → isConnectedFun n (λ (_ : X) → tt) → isConnected n X
isConnectedFun→isConnected n h =
  subst (isConnected n) (sym (typeToFiber _)) (h tt)

isConnected→isConnectedFun : {X : Type ℓ} (n : ℕ)
  → isConnected n X → isConnectedFun n (λ (_ : X) → tt)
isConnected→isConnectedFun n h = λ { tt → subst (isConnected n) (typeToFiber _) h }

isConnected0 : (X : Type ℓ) → isConnected 0 X
isConnected0 X = isContrUnit*

SuspUnit≃ : Susp Unit ≃ Unit
SuspUnit≃ = isoToEquiv i
  where
    open Iso
    i : Iso (Susp Unit) Unit
    i .fun _ = tt
    i .inv _ = north
    i .rightInv _ = refl
    i .leftInv north = refl
    i .leftInv south = merid tt
    i .leftInv (merid tt j) k = merid tt (j ∧ k)

isConnectedSphere : (n : ℕ) → isConnectedFun n (λ (_ : S (-1+ n)) → tt)
isConnectedSphere 0 =
  isConnected→isConnectedFun {X = S (-1+ 0)} 0 (isConnected0 (S (-1+ 0)))
isConnectedSphere (suc m) =
  isConnectedComp (λ (_ : Susp Unit) → tt) (suspFun (λ (_ : S (-1+ m)) → tt))
    (suc m) (isEquiv→isConnected _ (equivIsEquiv SuspUnit≃) _)
    (isConnectedSuspFun _ _ (isConnectedSphere m))

isConnectedFunLE : {A : Type ℓ} {B : Type ℓ'} (n m : HLevel) (f : A → B)
  → n ≤ m → isConnectedFun m f → isConnectedFun n f
isConnectedFunLE n m f hnm hf =
  isConnectedFunSubtr n (hnm .fst) f
  (subst (λ d → isConnectedFun d f) (sym (hnm .snd)) hf)

-- TODO: Would like to have some abstraction over pullbacks here.
isConnected-map-× : {A B B' : Type ℓ} (n : HLevel) (f : B → B')
  → isConnectedFun n f → isConnectedFun n (map-× (idfun A) f)
isConnected-map-× n f hf y@(a , b') =
  subst (isConnected n) (isoToPath i) (hf b')
  where
    open Iso
    i : Iso (fiber f b') (fiber (map-× (idfun _) f) y)
    i .fun z .fst .fst = a
    i .fun z .fst .snd = z .fst
    i .fun z .snd = ≡-× refl (z .snd)
    i .inv z .fst = z .fst .snd
    i .inv z .snd = cong snd (z .snd)
    i .rightInv ((az , bz) , e) j .fst .fst = cong fst e (~ j)
    i .rightInv ((az , bz) , e) j .fst .snd = bz
    i .rightInv ((az , bz) , e) j .snd k .fst = cong fst e (k ∨ ~ j)
    i .rightInv ((az , bz) , e) j .snd k .snd = cong snd e k
    i .leftInv z = refl

isConnectedSuc→isSurjection : {A : Type ℓ} {B : Type ℓ'} {f : A → B} {n : ℕ}
  → isConnectedFun (suc n) f → isSurjection f
isConnectedSuc→isSurjection hf b =
  Iso.inv propTruncTrunc1Iso (isConnectedFunLE 1 _ _ (suc-≤-suc zero-≤) hf b .fst)

-- Lifting from spheres
-- TODO: This could be a special case of lifting from CW complexes,
-- which we eventually need anyways.
liftSphereOfIsConnectedFun : (n : ℕ) {A B : Type ℓ} (f : A → B)
  → isConnectedFun n f → (k : S (-1+ n) → B) → ∃[ l ∈ (S (-1+ n) → A) ] k ≡ f ∘ l
liftSphereOfIsConnectedFun 0 f _ _ = ∣ Empty.rec , funExt (λ p → Empty.rec p) ∣₁
liftSphereOfIsConnectedFun (suc m) {A = A} f hf k = do
  (lN , hlN) ← isConnectedSuc→isSurjection hf (k north)
  (lS , hlS) ← isConnectedSuc→isSurjection hf (k south)
  (l' , hl') ← liftSphereOfIsConnectedFun m {A = lN ≡ lS} (cong f) (isConnectedCong m f hf)
    λ s → hlN ∙∙ cong k (merid s) ∙∙ sym hlS
  return ((λ { north → lN ; south → lS ; (merid s i) → l' s i }) ,
          λ { j north → hlN (~ j) ; j south → hlS (~ j) ; j (merid s i) →
                subst (PathP (λ j → hlN (~ j) ≡ hlS (~ j)) (cong k (merid s))) (funExt⁻ hl' s)
                (doubleCompPath-filler hlN (cong k (merid s)) (sym hlS)) j i })

-- TODO: golf this pair with a module
liftSpheresOfIsConnectedFun' : (N n : ℕ) {A B : Type ℓ} (f : A → B)
  → isConnectedFun n f → (k : FinData N × S (-1+ n) → B) → ∃[ l ∈ (FinData N × S (-1+ n) → A) ] k ≡ f ∘ l
liftSpheresOfIsConnectedFun' N n {A = A} f hf k =
  recFin {P = λ i → (Σ[ l ∈ (S (-1+ n) → A) ] (λ p → k (i , p)) ≡ f ∘ l)}
  isPropPropTrunc
  (λ li → ∣ (λ (i , p) → li i .fst p) , (funExt λ (i , p) → funExt⁻ (li i .snd) p) ∣₁)
  λ i → liftSphereOfIsConnectedFun n f hf (λ p → k (i , p))

liftSpheresOfIsConnectedFun : (N n : ℕ) {A B : Type ℓ} (f : A → B)
  → isConnectedFun n f → (k : Fin N × S (-1+ n) → B) → ∃[ l ∈ (Fin N × S (-1+ n) → A) ] k ≡ f ∘ l
liftSpheresOfIsConnectedFun N =
  subst
  (λ F → (n : ℕ) {A B : Type _} (f : A → B) →
    isConnectedFun n f → (k : F × S (-1+ n) → B) → ∃[ l ∈ (F × S (-1+ n) → A) ] k ≡ f ∘ l)
  (FinData≡Fin N) (liftSpheresOfIsConnectedFun' N)

module _ (d e : ℕ) where
  rangeFamily : Family
  rangeFamily .Ix = Σ[ n ∈ ℕ ] (d ≤ n) × (n < e)
  rangeFamily .A n = S (-1+ (n .fst))
  rangeFamily .B n = Unit
  rangeFamily .j n = λ _ → tt

  rangeFamilyConnected : (m : ℕ) → (m ≤ d) → FamilyConnected rangeFamily m
  rangeFamilyConnected m hmd (n , hdn , _) =
    isConnectedFunLE _ n _ (≤-trans hmd hdn) (isConnectedSphere n)

rangeFamilyGenerates : (d e d' e' : ℕ) (hd : d ≤ d') (he : e' ≤ e) →
  FamilyGenerates (rangeFamily d e) (rangeFamily d' e')
rangeFamilyGenerates d e d' e' hd he (i , hd'i , hie') =
  isRCC-base _ (i , ≤-trans hd hd'i , <≤-trans hie' he)

module _ (d : ℕ) where
  -- TODO: Naming

  -- A single d-cell
  oneCell : S (-1+ d) → Unit
  oneCell _ = tt

  NCells : (N : ℕ) → (Fin N × S (-1+ d)) → (Fin N × Unit)
  NCells N = map-× (idfun (Fin N)) oneCell

  -- In fact, the maps are equivalent in the arrow category.
  addCells : (N₁ N₂ : ℕ) → isPushoutOf (NCells (N₁ + N₂)) (map⊎ (NCells N₁) (NCells N₂))
  addCells N₁ N₂ = ipoOfPO (equivIsPushout {α = α} (equivIsEquiv q) (equivIsEquiv q))
    where
      q : {X : Type ℓ} → Fin (N₁ + N₂) × X ≃ ((Fin N₁ × X) ⊎ (Fin N₂ × X))
      q {X = X} =
          Fin (N₁ + N₂) × X
        ≃⟨ ≃-× (isoToEquiv (Fin+≅Fin⊎Fin N₁ N₂)) (idEquiv X) ⟩
          _
        ≃⟨ Σ⊎≃ ⟩
          ((Fin N₁ × X) ⊎ (Fin N₂ × X)) ■

      α : {X Y : Type ℓ} {f : X → Y} →
        equivFun q ∘ map-× (idfun _) f ≡ map⊎ (map-× (idfun _) f) (map-× (idfun _) f) ∘ equivFun q
      α = funExt p
        where
          p : _
          p ((i , _) , _) with i ≤? N₁
          ... | inl _ = refl
          ... | inr _ = refl

  addCells' : (N₁ N₂ : ℕ) → isPushoutOf (map⊎ (NCells N₁) (NCells N₂)) (NCells (N₁ + N₂))
  addCells' N₁ N₂ = ipoOfPO (equivIsPushout {α = α} (equivIsEquiv q) (equivIsEquiv q))
    where
      q : {X : Type ℓ} → ((Fin N₁ × X) ⊎ (Fin N₂ × X)) ≃ Fin (N₁ + N₂) × X
      q {X = X} =
          ((Fin N₁ × X) ⊎ (Fin N₂ × X))
        ≃⟨ isoToEquiv (invIso Σ⊎Iso) ⟩
          _
        ≃⟨ ≃-× (isoToEquiv (invIso (Fin+≅Fin⊎Fin N₁ N₂))) (idEquiv X) ⟩
          Fin (N₁ + N₂) × X
        ■

      α : {X Y : Type ℓ} {f : X → Y} →
        equivFun q ∘ map⊎ (map-× (idfun _) f) (map-× (idfun _) f) ≡ map-× (idfun _) f ∘ equivFun q
      α = funExt p
        where
          p : _
          p (inl _) = refl
          p (inr _) = refl

  isPushout0 : {X Y : Type} {f : X → Y} → isEquiv f → isPushoutOf (NCells 0) f
  isPushout0 hf .fst p = Empty.rec (¬Fin0 (p .fst))
  isPushout0 hf .snd .fst p = Empty.rec (¬Fin0 (p .fst))
  isPushout0 hf .snd .snd .fst = funExt λ p → Empty.rec (¬Fin0 (p .fst))
  isPushout0 hf .snd .snd .snd = equivIsPushout' (isoToIsEquiv i) hf
    where
      open Iso
      i : {A B : Type} {f : (Fin 0 × A) → (Fin 0 × B)} → Iso (Fin 0 × A) (Fin 0 × B)
      i {f = f} .fun = f
      i .inv p = Empty.rec (¬Fin0 (p .fst))
      i .rightInv p = Empty.rec (¬Fin0 (p .fst))
      i .leftInv p = Empty.rec (¬Fin0 (p .fst))

  isPushout1 : isPushoutOf (NCells 1) oneCell
  isPushout1 .fst = snd
  isPushout1 .snd .fst = snd
  isPushout1 .snd .snd .fst = refl
  isPushout1 .snd .snd .snd = equivIsPushout (isoToIsEquiv i) (isoToIsEquiv i)
    where
      open Iso
      i : {A : Type} → Iso (Fin 1 × A) A
      i .fun = snd
      i .inv a = (0 , a)
      i .rightInv a = refl
      i .leftInv a = ≡-× (isContr→isProp isContrFin1 _ _) refl

  module _ (e : ℕ) where
    record GoodFactorization {X Y : Type} (f : X → Y) : Type₁ where
      no-eta-equality
      field
        X' : Type
        g : X → X'
        h : X' → Y
        hf : f ≡ h ∘ g
        N : ℕ
        hg : isPushoutOf (NCells N) g
        hh : isRelativeCellComplex (rangeFamily (suc d) e) h

    HasGoodFactorization : {X Y : Type} → (X → Y) → Type₁
    HasGoodFactorization f = ∥ GoodFactorization f ∥₁

    open GoodFactorization
    open Iso

    HasGoodFactorization-id : {X : Type} → HasGoodFactorization (idfun X)
    HasGoodFactorization-id {X = X} = ∣ r ∣₁
      where
        r : GoodFactorization (idfun X)
        r .X' = X
        r .g = idfun X
        r .h = idfun X
        r .hf = refl
        r .N = 0
        r .hg = isPushout0 (idIsEquiv X)
        r .hh = isRCC-idfun _

    conn-GoodFactorization : {X Y : Type} (f : X → Y) → GoodFactorization f →
      isConnectedFun d f
    conn-GoodFactorization f ff = subst (isConnectedFun _) (sym (ff .hf))
      (isConnectedComp (ff .h) (ff .g) _
        (conn-isRCC (rangeFamily (suc d) e) (rangeFamilyConnected (suc d) e d ≤-sucℕ) (ff .hh))
        (isConnectedPushout d (ff .hg) (isConnected-map-× d _ (isConnectedSphere d))))

    HasGoodFactorization-comp : {X Y Z : Type} (f₁ : X → Y) (f₂ : Y → Z)
      → HasGoodFactorization f₁ → HasGoodFactorization f₂ → HasGoodFactorization (f₂ ∘ f₁)
    HasGoodFactorization-comp {X} {Y} {Z} f₁ f₂ hf₁ hf₂ = do
      ff₁ ← hf₁
      ff₂ ← hf₂
      (l , hl) ← liftSpheresOfIsConnectedFun _ _ f₁ (conn-GoodFactorization f₁ ff₁) (ff₂ .hg .fst)
      return (finish ff₁ ff₂ l (hl ∙ (ff₁ .hf ▹ l)))
      where
        finish : (ff₁ : GoodFactorization f₁) → (ff₂ : GoodFactorization f₂)
          → (l : (Fin (ff₂ .N) × S (-1+ d)) → X) → (ff₂ .hg .fst ≡ ff₁ .h ∘ ff₁ .g ∘ l)
          → GoodFactorization (f₂ ∘ f₁)
        finish ff₁ ff₂ l hl = r
          where
            open Recombination _ _ (ff₁ .g) (ff₁ .h) (ff₂ .g) (ff₁ .hg) (ff₂ .hg) l (sym hl)
            r : GoodFactorization (f₂ ∘ f₁)
            r .X' = X''
            r .g = f'
            r .h = ff₂ .h ∘ g'
            r .hf = (f₂ ◃ ff₁ .hf) ∙ (ff₂ .hf ▹ _) ∙ (ff₂ .h ◃ q)
            r .N = ff₁ .N + ff₂ .N
            r .hg = comp-isPushoutOf (addCells _ _) hf'
            r .hh = isRCC-comp _ (isRCC-po _ hg' (ff₁ .hh)) (ff₂ .hh)

    HasGoodFactorization-po : {X Y X₁ : Type} (f : X → Y) (k : X → X₁)
      → HasGoodFactorization f → HasGoodFactorization {Y = Pushout f k} inr
    HasGoodFactorization-po {X = X} {Y = Y} {X₁ = X₁} f k = map GF
      where
        GF : GoodFactorization f → GoodFactorization inr
        GF ff = r
          where
            s =
              cancel-isPushoutAlong'' {g₁ = ff .h}
                (PushoutIsPushout (ff .g) k)
                (paste'IsPushout (equivIsPushout {α = sym (ff .hf)} (idIsEquiv X) (idIsEquiv Y)) (PushoutIsPushout f k))

            r : GoodFactorization inr
            r .X' = Pushout (ff .g) k
            r .g = inr
            r .h = s .fst
            r .hf = s .snd .fst
            r .N = ff .N
            r .hg = comp-isPushoutOf (ff .hg) isPushoutOfInr
            r .hh = isRCC-po _ (_ , _ , _ , s .snd .snd .snd) (ff .hh)

    HasGoodFactorization-cell : (i : Σ[ n ∈ ℕ ] (d ≤ n) × (n < e))
      → HasGoodFactorization (λ (_ : S (-1+ i .fst)) → tt)
    HasGoodFactorization-cell i with ≤-split (i .snd .fst)
    ... | (inl hlt) = ∣ r ∣₁
      where
        r : GoodFactorization (λ (_ : S (-1+ i .fst)) → tt)
        r .X' = S (-1+ i .fst)
        r .g = idfun _
        r .h = λ _ → tt
        r .hf = refl
        r .N = 0
        r .hg = isPushout0 (idIsEquiv _)
        r .hh = isRCC-base (rangeFamily (suc d) e) (i .fst , hlt , i .snd .snd)
    ... | (inr heq) = subst (λ m → HasGoodFactorization (λ (_ : S (-1+ m)) → tt)) heq ∣ r ∣₁
      where
        r : GoodFactorization (λ (_ : S (-1+ d)) → tt)
        r .X' = Unit
        r .g = oneCell
        r .h = idfun Unit
        r .hf = refl
        r .N = 1
        r .hg = isPushout1
        r .hh = isRCC-idfun _

    hasGoodFactorization : {X Y : Type} (f : X → Y) → isRelativeCellComplex (rangeFamily d e) f
      → HasGoodFactorization f
    hasGoodFactorization =
      isRCCElimProp _ HasGoodFactorization (λ _ → isPropPropTrunc)
      HasGoodFactorization-id
      HasGoodFactorization-comp
      (λ {i} → HasGoodFactorization-cell i)
      HasGoodFactorization-po
