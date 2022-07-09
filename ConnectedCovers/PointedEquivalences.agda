{-# OPTIONS --experimental-lossy-unification #-}
module ConnectedCovers.PointedEquivalences where

open import Cubical.Foundations.Everything

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.HITs.Truncation

open import FibCofibSeq

open import ConnectedCovers.TruncationLevelFacts

private
  variable
    ℓ : Level

AFamilyParametrised : (F : Pointed ℓ → Pointed ℓ) (f : (A : Pointed ℓ) → (A →∙ (F A))) → ({A* : Pointed ℓ} → typ A* → Type ℓ)
AFamilyParametrised F f {A* = A*} x = fst (f A*) x ≡ fst (f A*) (pt A*)

truncFam : (n : ℕ) → ({A* : Pointed ℓ} → typ A* → Type ℓ)
truncFam n {A* = A*} = AFamilyParametrised (hLevelTrunc∙ n) (λ A → trunc∙ n) {A* = A*}

ΣFamBaseChange : (A A' : Pointed ℓ) (F : Pointed ℓ → Pointed ℓ) (f : (A : Pointed ℓ) → (A →∙ (F A))) → (A ≃∙ A')
  → (Σ (typ A) (AFamilyParametrised F f {A* = A}) , (pt A , refl))
   ≃∙ (Σ (typ A') (AFamilyParametrised F f {A* = A'}) , (pt A' , refl))
ΣFamBaseChange A A' F f =
 Equiv∙J
 (λ A'' e' → (Σ (typ A'') (AFamilyParametrised F f {A* = A''}) , (pt A'' , refl)) ≃∙ (Σ (typ A') (AFamilyParametrised F f {A* = A'}) , (pt A' , refl)))
 (idEquiv _ , refl)


ΣAssoc∙ : (A : Pointed ℓ) (B : typ A → Type ℓ)
  (C : (a : typ A) → B a → Type ℓ) (b' : B (pt A)) (c' : C (pt A) b')
  → (Σ (Σ (typ A) B) (λ (a , b) → C a b) , ((pt A) , b') , c')
  ≃∙ Σ (typ A) (λ a → Σ (B a) (C a)) , (pt A) , (b' , c')
fst (ΣAssoc∙ A B C b' c') = Σ-assoc-≃
snd (ΣAssoc∙ A B C b' c') = refl

trunc≡Equiv∙ : (A : Pointed ℓ) (n : ℕ)
  → ((trunc {X = A} (2 + n) (pt A) ≡ trunc (2 + n) (pt A)) , refl)
  ≃∙ hLevelTrunc∙ (suc n) ((pt A ≡ pt A) , refl)
fst (trunc≡Equiv∙ A n) = isoToEquiv (PathIdTruncIso (suc n))
snd (trunc≡Equiv∙ A n) = cong ∣_∣ (transportRefl refl)

ΣSwapNested : (A : Type ℓ) (B : Type ℓ) (C : A → B → Type ℓ)
  → (Σ A (λ a → Σ B (C a))) ≃ (Σ B (λ b → Σ A (λ a → C a b)))
ΣSwapNested A B C =
  invEquiv Σ-assoc-≃
  ∙ₑ Σ-cong-equiv-fst Σ-swap-≃
  ∙ₑ Σ-assoc-≃

ΣSwap∙ : (A : Type ℓ) (B : Type ℓ) (C : A → B → Type ℓ) (a : A) (b : B)
  (c : C a b) → (Σ A (λ a → Σ B (C a)) , (a , (b , c))) ≃∙ (Σ B (λ b → Σ A (λ a → C a b)) , (b , (a , c)))
fst (ΣSwap∙ A B C a b c) =
  invEquiv (fst (ΣAssoc∙ (A , a) (λ _ → B) C b c))
  ∙ₑ Σ-cong-equiv-fst Σ-swap-≃
  ∙ₑ fst (ΣAssoc∙ (B , b) (λ _ → A) (λ b' a' → C a' b') a c)
snd (ΣSwap∙ A B C a b c) = refl


ΣContr∙ : (A : Type ℓ) (B : A → Type ℓ) (a : A) (b : B a) → ((a' : A) → isContr (B a')) → (Σ A B , (a , b)) ≃∙ (A , a)
fst (ΣContr∙ A B a b contrB) = Σ-contractSnd contrB
snd (ΣContr∙ A B a b contrB) = refl


ΣPtdFibEq : (A : Pointed ℓ) (B B' : (typ A) → Type ℓ) (b : B (pt A))
  (b' : B' (pt A))
  (e : (a : typ A) → B a ≃ B' a) → (fst (e (pt A)) b ≡ b')
  → (Σ (typ A) B , (pt A , b)) ≃∙ (Σ (typ A) B' , (pt A , b'))
fst (ΣPtdFibEq A B B' b b' e p) = Σ-cong-equiv-snd e
snd (ΣPtdFibEq A B B' b b' e p) = ΣPathP (refl , p)


ua∙' : (A B : Pointed ℓ) → A ≃∙ B → A ≡ B
ua∙' A B = Equiv∙J (λ A' e' → A' ≡ B) refl

ua∙* : (A B : Pointed ℓ) → A ≃∙ B → A ≡ B
ua∙* A B e = ua∙ (fst e) (snd e)

au∙ : (A B : Pointed ℓ) → A ≡ B → A ≃∙ B
au∙ A B = J (λ A' p' → A ≃∙ A') ((idEquiv (typ A)) , refl)

