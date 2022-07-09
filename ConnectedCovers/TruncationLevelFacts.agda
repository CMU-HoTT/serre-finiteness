module ConnectedCovers.TruncationLevelFacts where

open import Cubical.Foundations.Everything

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Data.Nat
open import Cubical.Data.Sigma.Properties
open import Cubical.HITs.Truncation
open import Cubical.Homotopy.Connected

open import HomotopyGroups

private
  variable
    ℓ : Level

equivToContr : {A B : Type ℓ} (e : A ≃ B) → isContr B → isContr A
equivToContr =
 EquivJ (λ A e → isContr _ → isContr A) λ x → x

singl' : {A : Type ℓ} (a : A) → Type ℓ
singl' a = Σ _ (λ x → x ≡ a)

transportlemma : {A : Type ℓ} {a x : A} (p : x ≡ a)
  → transport (λ i → (p ⁻¹) i ≡ a) (λ _ → a) ≡ p
transportlemma = J (λ y p → transport (λ i → (p ⁻¹) i ≡ y) refl ≡ p)
 (transportRefl refl)

isContrSingl' : {A : Type ℓ} (a : A) → isContr (singl' a)
fst (isContrSingl' a) = a , refl
snd (isContrSingl' a) (x , p) = ΣPathP ((p ⁻¹) ,
 toPathP (transportlemma p))

concatPathEq : {X : Type ℓ} {x y z : X} (p : x ≡ y) (q : x ≡ y) (r : x ≡ z)
  → (p ≡ q) ≃ ((r ⁻¹) ∙ p ≡ (r ⁻¹) ∙ q)
concatPathEq p q =
 J (λ z r → (p ≡ q) ≃ ((r ⁻¹) ∙ p ≡ (r ⁻¹) ∙ q))
   (compEquiv (compPathlEquiv (cong (_∙ p) (symRefl ⁻¹) ∙ (lUnit p) ⁻¹))
              (compPathrEquiv (lUnit q ∙ cong (_∙ q) symRefl)))

swapPathltr : {X : Type ℓ} {x y : X} (p : x ≡ y) (q : x ≡ y)
  → (q ⁻¹ ∙ p ≡ refl) ≃ (p ≡ q)
swapPathltr =
  J (λ y p → (q : _ ≡ y) → (q ⁻¹ ∙ p ≡ refl) ≃ (p ≡ q))
    λ q → concatPathEq (q ⁻¹ ∙ refl) refl (q ⁻¹) 
    ∙ₑ compEquiv
       (compPathlEquiv ((lCancel (q ⁻¹)) ⁻¹ ∙ cong ((q ⁻¹) ⁻¹ ∙_) (rUnit _)))
       (compPathrEquiv ((rUnit _) ⁻¹ ∙ (symInvo _) ⁻¹))

trunc∙ : {X : Pointed ℓ} (n : ℕ) → (X →∙ hLevelTrunc∙ n X)
trunc∙ zero = ∣_∣ₕ , refl
trunc∙ (suc n) = ∣_∣ₕ , refl

trunc : {X : Pointed ℓ} (n : ℕ) → typ X → typ (hLevelTrunc∙ n X)
trunc {X = X} n = fst (trunc∙ {X = X} n)

postulate
  AbGrpTruncEq : (X : Pointed ℓ) (n : ℕ) → AbGroupEquiv (πAb n (hLevelTrunc∙ (4 + n) X)) (πAb n X)

  ConnToHLevelTruncConn :(X : Type ℓ) (m n : ℕ) → isConnected n X → isConnected n (hLevelTrunc m X)


-- This is a fact about connected covers, but I'm keeping it here as
-- it doesn't use the definition
module _ (A : Pointed ℓ) (a : typ A) (n m : ℕ) where

 substlemma :
  (q : a ≡ pt A) (p : (trunc {X = A} (suc n) a) ≡ (trunc {X = A} (suc n) (pt A)))
  → subst (λ a' → trunc {X = A} (suc n) a' ≡ trunc {X = A} (suc n) (pt A))
     q p ≡ (cong ∣_∣ₕ q) ⁻¹ ∙ p
 substlemma =
  J (λ y q →
  (p : (trunc {X = A} (suc n) a) ≡ (trunc {X = A} (suc n) y))
  → subst (λ a' → trunc {X = A} (suc n) a' ≡ trunc {X = A} (suc n) y) q p
  ≡ (cong ∣_∣ₕ q) ⁻¹ ∙ p)
  λ p → transportRefl p ∙ lUnit p

 transportPathΣEquiv : (q : a ≡ pt A)
   → (Σ[ p ∈ (trunc {X = A} (suc n) a) ≡ (trunc {X = A} (suc n) (pt A)) ]
     (transport (λ i → (trunc {X = A} (suc n) (q i)) ≡ (trunc {X = A} (suc n) (pt A))) p) ≡ refl) ≃
      (Σ[ p ∈ (trunc {X = A} (suc n) a) ≡ (trunc {X = A} (suc n) (pt A)) ]
     (p ≡ cong ∣_∣ₕ q))
 transportPathΣEquiv q = Σ-cong-equiv-snd
  (λ p → compEquiv (compPathlEquiv ((substlemma q p) ⁻¹))
  (swapPathltr p (cong ∣_∣ₕ q)))


 transportOfPathPathContr : (q : a ≡ pt A)
  → isContr (Σ[ p  ∈ (trunc {X = A} (suc n) a) ≡ (trunc {X = A} (suc n) (pt A)) ]
     ((transport (λ i → (trunc {X = A} (suc n) (q i))
                     ≡ (trunc {X = A} (suc n) (pt A))) p) ≡ refl))
 transportOfPathPathContr q = equivToContr (transportPathΣEquiv q)
  (isContrSingl' (cong ∣_∣ₕ q))


