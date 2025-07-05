{-# OPTIONS --lossy-unification #-}
module CorollariesToGanea where

open import Everything

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.DirectProduct
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup
open import Cubical.Algebra.AbGroup.Instances.Int renaming (ℤAbGroup to ℤ)
open import Cubical.Algebra.AbGroup.Instances.IntMod renaming (ℤAbGroup/_ to ℤMod)

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.HITs.Join renaming (inl to inlj ; inr to inrj)
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.Loopspace

open import Connectedness
open import SAF
open import FPAbGroup
open import PointedHITs

open import FiberOrCofiberSequences.Base
open import FiberOrCofiberSequences.CofiberBase

private
  variable
    ℓ : Level

join∙^ : ℕ → (Pointed ℓ) → Pointed ℓ → Pointed ℓ
join∙^ zero F G = F
join∙^ (suc n) F G = join∙ (join∙^ n F G) G


module _ (F G : Pointed ℓ) where
  join∙^-connected : (n : ℕ)
                  → isConnected 1 (typ F)
                  → isConnected 1 (typ G)
                  → isConnected (suc n) (typ (join∙^ n F G))
  join∙^-connected zero cF cG = cF
  join∙^-connected (suc n) cF cG =
    transport (λ i → isConnected (+-comm (suc n) 1 i) (typ (join∙^ (suc n) F G)))
    (isConnectedJoin (suc n) 1 ((suc n) + 1) ≤-refl (join∙^-connected n cF cG) cG)

  join∙^-SNFnt : (m n : ℕ)
                 → isConnected 1 (typ F)
                 → stablyNFinite (suc n) F
                 → isConnected 1 (typ G)
                 → stablyNFinite (suc n) G
                 → stablyNFinite (suc m + n) (join∙^ m F G)
  join∙^-SNFnt zero n cF sF cG sG = sF
  join∙^-SNFnt (suc m) n cF sF cG sG =
    stablyNFiniteJoin (suc m) (suc m + n) 1 (suc n) order1 (join∙^-connected m cF cG) (join∙^-SNFnt m n cF sF cG sG) cG sG (suc (suc m + n)) order2 order3
     where
       -- i hate pink floyd

       order1 : suc m ≤ suc (m + n)
       order1 = suc-≤-suc ≤SumLeft

       postulate
         arthritis : suc (m + n) ≡ (m + n + 1)

       order2 : suc (suc (m + n)) ≤ suc (m + n + 1)
       order2 = suc-≤-suc (transport (λ i → suc (m + n) ≤ (arthritis i))
                                     ≤-refl)

       order3 : suc (suc (m + n)) ≤ suc (n + suc m)
       order3 = suc-≤-suc (transport (λ i → suc (m + n) ≤ (+-comm (suc m) n i))
                                    ≤-refl)
              

-- sillyy
postulate
  isConnected→mere-path : {X : Type ℓ} → isConnected 3 X
                                    → (x y : X)
                                    → ∥ x ≡ y ∥ 1

  isConnected→isConnectedFun* : (n : ℕ) {X : Type ℓ}
    → isConnected n X → isConnectedFun {ℓ} {ℓ} n (λ (_ : X) → tt*)

  pushoutFunEqIso : {A A' C : Type ℓ} {B : Type₀}
    (f : A → B) (g : A → C) (h : A' → B) (k : A' → C)
    (K : Iso A A')
    (q : f ≡ h ∘ Iso.fun K)
    (p : g ∘ Iso.inv K ≡ k)
    → Iso (Pushout f g) (Pushout h k)


  pushoutLevelMix : {ℓ' : Level} {A C : Type ℓ} {B C' : Type ℓ'}
     (f : A → B) (g : A → C) (g' : A → C')
     (K : Iso C C')
     (q : Iso.fun K ∘ g ≡ g')
     → Iso (Pushout f g) (Pushout f g')

  unitLevelMix : Iso (Unit* {ℓ}) (Unit)

  unitLevelMix' : {B : Type ℓ}
    → (λ (x : B) → (Iso.fun (unitLevelMix {ℓ})) ((λ (_ : B) → tt*) x))
    ≡ (λ (_ : B) → tt)
  
  join-iso-join : (X X' Y : Type ℓ)
    → Iso X X' → Iso (join X Y) (join X' Y)

  join-iso-join∙ : (X X' Y : Pointed ℓ) (H : Iso (typ X) (typ X'))
    (p : Iso.fun H (pt X) ≡ (pt X'))
    → Iso.fun (join-iso-join (typ X) (typ X') (typ Y) H) (pt (join∙ X Y))
       ≡ (pt (join∙ X' Y))

module Ganea^ {A : Pointed ℓ} {B : Pointed ℓ} (f : A →∙ B) where

  mutual
    E : ℕ → (Pointed ℓ)
    E zero = A
    E (suc n) = fib-cofib (p n) , inr (pt (E n))

    p : (n : ℕ) → (E n →∙ B)
    p zero = f
    p (suc n) = (GaneaMap (p n)) , (snd (p n))

  sntychk : (GaneaMap f) ≡ (fst (p 1))
  sntychk = refl

  F : ℕ → (Pointed ℓ)
  F zero = fiber (fst f) (pt B) , pt A , snd f
  F (suc n) = (GaneaFib (p n)) , ((pt (E (1 + n))) , snd (p n))

  join-F : ℕ → (Pointed ℓ)
  join-F n = join∙^ n (F 0) (Ω B)

  Ganea^Iso : (n : ℕ) → Iso (fst (F n)) (fst (join-F n))
  Ganea^Iso zero = idIso
  Ganea^Iso (suc zero) = GaneaIso f
  Ganea^Iso (suc (suc n)) =
    compIso (GaneaIso (p (suc n)))
            (join-iso-join (typ (F (suc n)))
                        (typ (join-F (suc n))) (typ (Ω B))
                        (Ganea^Iso (suc n)))

  Ganea^≡ : (n : ℕ) → (fst (F n)) ≡ (fst (join-F n))
  Ganea^≡ n = ua (isoToEquiv (Ganea^Iso n))

  Ganea^Iso∙ : (n : ℕ) → Iso.fun (Ganea^Iso n) (pt (F n)) ≡ (pt (join-F n))
  Ganea^Iso∙ zero = refl
  Ganea^Iso∙ (suc zero) = refl
  Ganea^Iso∙ (suc (suc n)) =
    join-iso-join∙ (F (suc n)) (join-F (suc n)) (Ω B)
                   (Ganea^Iso (suc n)) (Ganea^Iso∙ (suc n))


  Ganea^≃∙ : (n : ℕ) → (F n) ≃∙ (join-F n)
  fst (Ganea^≃∙ n) = isoToEquiv (Ganea^Iso n)
  snd (Ganea^≃∙ n) = Ganea^Iso∙ n

  Ganea^≡∙ : (n : ℕ) → (F n) ≡ (join-F n)
  Ganea^≡∙ n = ua∙ (fst (Ganea^≃∙ n)) (snd (Ganea^≃∙ n))

  GaneaCofiberSeq'₋ : (n : ℕ) → CofiberSeq₋ (typ (F n)) (typ (E n))
                                           (typ (E (1 + n)) , inl tt)
  GaneaCofiberSeq'₋ zero = cofiber-CofiberSeq₋ fst
  GaneaCofiberSeq'₋ (suc n) = cofiber-CofiberSeq₋ fst

  GaneaCofiberSeq''₋ : (n : ℕ) → CofiberSeq₋ (typ (F n)) (typ (E n))
                                    (E (1 + n))
  GaneaCofiberSeq''₋ n = transport (λ i → CofiberSeq₋ (typ (F n)) (typ (E n))
                                                (fib-cofib (p n) , push (pt (E n) , (snd (p n))) i))
                                                (GaneaCofiberSeq'₋ n)

  GaneaCofiberSeq₋ : (n : ℕ) → CofiberSeq₋ (typ (join-F n)) (typ (E n))
                                            (E (1 + n))
  GaneaCofiberSeq₋ n = transport (λ i → CofiberSeq₋ (Ganea^≡ n i) (typ (E n))
                                                     (E (1 + n)))
                                  (GaneaCofiberSeq''₋ n)

  GaneaCofiberSeq' : (n : ℕ) → CofiberSeq (F n) (E n)
                                           (typ (E (1 + n)) , inl tt)
  GaneaCofiberSeq' zero = CofiberSeq₋→CofiberSeq (GaneaCofiberSeq'₋ 0)
                          (transport (λ i → (cofiber-CofiberSeqInc₋ fst i)
                            (pt (F 0)) ≡ pt A) refl)
  GaneaCofiberSeq' (suc n) =
    CofiberSeq₋→CofiberSeq (GaneaCofiberSeq'₋ (suc n))
       (transport (λ i → (cofiber-CofiberSeqInc₋ fst i)
                          (pt (F (suc n))) ≡ pt (E (suc n))) refl)

  GaneaCofiberSeq'' : (n : ℕ) → CofiberSeq (F n) (E n)
                                    (E (1 + n))
  GaneaCofiberSeq'' n = transport (λ i → CofiberSeq (F n) (E n)
                                                (fib-cofib (p n) , push (pt (E n) , (snd (p n))) i))
                                                (GaneaCofiberSeq' n)

  GaneaCofiberSeq : (n : ℕ) → CofiberSeq (join-F n) (E n)
                                          (E (1 + n))
  GaneaCofiberSeq n =
    transport
      (λ i → CofiberSeq (ua∙ (fst (Ganea^≃∙ n)) (snd (Ganea^≃∙ n)) i)
                         (E n) (E (1 + n)))
      (GaneaCofiberSeq'' n)

postulate
  safΩ→saf : {B : Pointed ℓ} (cB : isConnected 2 (typ B)) → saf (Ω B) → saf B


saf→safΩ : {B : Pointed ℓ} (scB : isConnected 3 (typ B)) → saf B → saf (Ω B)
saf→safΩ {ℓ} {B} scB hB = γ
  where
    open Ganea^ ((λ (_ : Unit*) → (pt B)) , refl)

    ΩB-stably2Finite : stablyNFinite 2 (Ω B)
    ΩB-stably2Finite = stablyNFiniteApprox' ((λ _ → tt*) , refl) 2
      (isConnected→isConnectedFun* 2 (isConnectedPath 2 scB (pt B) (pt B)))
                                      (saf-Unit 2)

    F0-Iso : Iso (typ (F 0)) (typ (Ω B))
    Iso.fun F0-Iso (tt* , p) = p
    Iso.inv F0-Iso p = tt* , p
    Iso.rightInv F0-Iso = λ _ → refl
    Iso.leftInv F0-Iso = λ _ → refl

    F0-Eq∙ : (F 0) ≃∙ (Ω B)
    fst F0-Eq∙ = isoToEquiv F0-Iso
    snd F0-Eq∙ = refl

    F0-≡ : (F 0) ≡ (Ω B)
    F0-≡ = ua∙ (fst F0-Eq∙) (snd F0-Eq∙)

    connected-join-F : (k : ℕ) → isConnected 2 (typ (join-F k))
    connected-join-F zero =
      transport (λ i → isConnected 2 (typ (F0-≡ (~ i))))
                (isConnectedPath 2 scB (pt B) (pt B))
    connected-join-F (suc k) =
      isConnectedJoin 1 1 2 ≤-refl
        (isConnectedSubtr 1 1 (connected-join-F k))
        (isConnectedSubtr 1 1 (isConnectedPath 2 scB (pt B) (pt B)))

    connected-join-F' : (k : ℕ) → isConnected (suc (suc k))
                                               (typ (join-F (suc k)))
    connected-join-F' k = join∙^-connected (F 0) (Ω B) (suc k)
      (transport (λ i → isConnected 1 (typ (F0-≡ (~ i))))
                 (isConnectedSubtr 1 1 (isConnectedPath 2 scB (pt B) (pt B))))
                   (isConnectedSubtr 1 1 (isConnectedPath 2 scB (pt B) (pt B)))

    connected-p : (k : ℕ) → isConnectedFun (suc (suc k))
                                            (fst (p (suc k)))
    connected-p k b =
      rec isPropIsContr
       (λ q → transport (λ i → isConnected (suc (suc k))
       (fiber (fst (p (suc k))) (q i)))
       (transport (λ i → isConnected (suc (suc k))
       (Ganea^≡ (suc k) (~ i))) (connected-join-F' k)))
       (isConnected→mere-path scB (pt B) b)

    ΩB→Fn-stablyNFinite : (n : ℕ) → stablyNFinite (2 + n) (Ω B)
      → (k : ℕ) → stablyNFinite (4 + n) (F (1 + k))
    ΩB→Fn-stablyNFinite n sΩB zero =
      transport (λ i → stablyNFinite (4 + n) (Ganea^≡∙ 1 (~ i)))
                (stablyNFiniteJoin 2 (2 + n) 2 (2 + n)
                (suc-≤-suc (suc-≤-suc zero-≤))
                (transport (λ i → isConnected 2 (typ (F0-≡ (~ i))))
                           (isConnectedPath 2 scB (pt B) (pt B)))
                (transport (λ i → stablyNFinite (2 + n) (F0-≡ (~ i)))
                           sΩB)
                (isConnectedPath 2 scB (pt B) (pt B)) sΩB (4 + n)
                (suc-≤-suc (suc-≤-suc
                  (transport (λ i → 2 + n ≤ (+-comm 2 n i)) ≤-refl)))
                (suc-≤-suc (suc-≤-suc
                  (transport (λ i → 2 + n ≤ (+-comm 2 n i)) ≤-refl))))
    ΩB→Fn-stablyNFinite n sΩB (suc k) =
      transport (λ i → stablyNFinite (4 + n) (Ganea^≡∙ (2 + k) (~ i)))
                (stablyNFiniteJoin 2 (2 + n) 2 (2 + n)
                (suc-≤-suc (suc-≤-suc zero-≤))
                (connected-join-F (suc k))
                (stablyNFiniteDrop (2 + n)
                 (stablyNFiniteDrop (1 + (2 + n))
                  (transport (λ i → stablyNFinite (suc (suc (suc (suc n))))
                                     (Ganea^≡∙ (1 + k) i))
                             (ΩB→Fn-stablyNFinite n sΩB k))))
                (isConnectedPath 2 scB (pt B) (pt B)) sΩB (4 + n)
                (suc-≤-suc (suc-≤-suc
                  (transport (λ i → 2 + n ≤ (+-comm 2 n i)) ≤-refl)))
                (suc-≤-suc (suc-≤-suc
                  (transport (λ i → 2 + n ≤ (+-comm 2 n i)) ≤-refl))))


    eventuallySNFnt : (n k : ℕ) → stablyNFinite (2 + n) (Ω B)
                                → stablyNFinite (4 + n) (E (suc k))
                                → stablyNFinite (4 + n) (E 1)
    eventuallySNFnt n zero sΩB hyp = hyp
    eventuallySNFnt n (suc k) sΩB hyp =
      eventuallySNFnt n k sΩB
        (stablyNFiniteExtension
          (GaneaCofiberSeq (suc k))
           (transport (λ i → stablyNFinite (suc (suc (suc (suc n))))
                              (Ganea^≡∙ (suc k) i))
                      (ΩB→Fn-stablyNFinite n sΩB k))
            hyp)
      

    E1-Iso'' : Iso (typ (E 1)) (Pushout {C = Unit* {ℓ}}
                                        (λ (_ : typ (Ω B)) → tt)
                                        (λ _ → tt*))
    E1-Iso'' = pushoutFunEqIso (λ _ → tt) (λ _ → tt*)
                 (λ _ → tt) (λ r → tt*) F0-Iso refl refl
    
    E1-Iso' : Iso (typ (E 1)) (PushoutSusp (typ (Ω B)))
    E1-Iso' = compIso E1-Iso''
              (pushoutLevelMix (λ _ → tt) (λ _ → tt*) (λ _ → tt)
                unitLevelMix unitLevelMix')

    E1-Iso : Iso (typ (E 1)) (Susp (typ (Ω B)))
    E1-Iso = compIso E1-Iso' PushoutSuspIsoSusp

    E1-≡ : (typ (E 1)) ≡ (Susp (typ (Ω B)))
    E1-≡ = ua (isoToEquiv E1-Iso)

    E1→SuspΩB-SNFnt : (n : ℕ) → stablyNFinite n (E 1)
                               → (stablyNFinite n (S∙ (Ω B)))
    E1→SuspΩB-SNFnt n hyp = pointIrrelSNFnt n
      ((Susp (typ (Ω B))) , (Iso.fun (E1-Iso) (pt {ℓ} (E 1))))
      (pt (S∙ (Ω B))) (transport (λ i → stablyNFinite n
      (ua∙ {A = (E 1)} {B = Susp (typ (Ω B)) , fst (isoToEquiv E1-Iso)
      (snd (E 1))} (isoToEquiv E1-Iso) (refl) i)) hyp)

    γ : saf (Ω B)
    γ 0 = stablyNFiniteDrop 0 (stablyNFiniteDrop 1 ΩB-stably2Finite)
    γ 1 = stablyNFiniteDrop 1 ΩB-stably2Finite
    γ 2 = ΩB-stably2Finite
    γ (suc (suc (suc n))) =
      stablyNFiniteOfSusp (3 + n) (Ω B)
       (E1→SuspΩB-SNFnt (4 + n)
         (eventuallySNFnt n (2 + n) (γ (suc (suc n)))
           (stablyNFiniteApprox' (p (3 + n)) (4 + n)
            (connected-p (2 + n)) (hB (4 + n)))))
    

postulate
  safTotal : {F E B : Pointed ℓ} (S : FiberSeq F E B) (scB : isConnected 3 (typ B))
    → saf B → saf F → saf E

EMℤMod-saf : (n m : ℕ) → saf {ℓ = ℓ-zero} (EM∙ (ℤMod (suc n)) (suc m))
EMℤMod-saf n zero = safΩ→saf (isConnectedEM 1)
                    (transport (λ i → saf (EM≃ΩEM+1∙ {G = ℤMod (suc n)} 0 i))
                    (transport (λ i → saf (ua∙ {A = EM∙ (ℤMod (suc n)) 0}
                                               (ℤMod-finite n) refl (~ i)))
                               (saf-Fin (suc n) _)))
EMℤMod-saf n (suc m) =
  safΩ→saf (isConnectedSubtr 2 (1 + m)
               (transport (λ i → isConnected (+-comm 2 (1 + m) i)
                                    (typ (EM∙ (ℤMod (suc n)) (suc (suc m)))))
                          (isConnectedEM (2 + m))))
            (transport (λ i → saf (EM≃ΩEM+1∙ {G = ℤMod (suc n)} (suc m) i))
                       (EMℤMod-saf n m))

EMℤ-saf : (m : ℕ) → saf {ℓ = ℓ-zero} (EM∙ ℤ (suc m))
EMℤ-saf zero = transport (λ i → saf (EM₁ℤ (~ i)))
                         (saf-Sn 1)
EMℤ-saf (suc m) =
  safΩ→saf (isConnectedSubtr 2 (1 + m)
               (transport (λ i → isConnected (+-comm 2 (1 + m) i)
                                    (typ (EM∙ ℤ (2 + m))))
                          (isConnectedEM (2 + m))))
               (transport (λ i → saf (EM≃ΩEM+1∙ {G = ℤ} (suc m) i))
                         (EMℤ-saf m))

saf-dir-prod : (H K : AbGroup ℓ)
  → ((n : ℕ) → saf (EM∙ H (suc n)))
  → ((n : ℕ) → saf (EM∙ K (suc n)))
  → (n : ℕ)
  → saf (EM∙ (AbDirProd H K) (suc n))
saf-dir-prod H K hH hK n =
  transport (λ i → saf (EMDirProd H K (suc n) (~ i)))
            (saf× (hH n) (hK n))

isFP→safEM : (A : AbGroup ℓ-zero) (fpA : isFP A) (n : ℕ)
  → saf (EM∙ A (suc n))
isFP→safEM =
  indFP (λ A → (n : ℕ) → saf (EM∙ A (suc n)))
        (λ A → isOfHLevelΠ 1 λ n → saf-isProp {X = EM∙ A (suc n)})
        (λ { zero m → EMℤ-saf m ; (suc n) m → EMℤMod-saf n m})
        saf-dir-prod
