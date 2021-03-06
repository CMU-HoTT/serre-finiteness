module ConnectedCovers.Base where

open import Cubical.Foundations.Everything

open import Cubical.Data.Empty renaming (rec to rec⊥)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.HITs.Truncation
open import Cubical.Homotopy.Connected
open import Cubical.Relation.Nullary.Base

open import HomotopyGroups
open import FibCofibSeq

open import ConnectedCovers.PointedEquivalences
open import ConnectedCovers.TruncationLevelFacts

private
  variable
    ℓ : Level


truncIsConnected : (X : Pointed ℓ) (n : ℕ) → isConnectedFun n (trunc {X = X} n)
truncIsConnected X n = {!!}

-- n+2 (or n, depending on the convention) connected cover
_⦉_⦊ : (X : Pointed ℓ) → ℕ → Pointed ℓ
X ⦉ zero ⦊ = fiber∙ {A = X} (trunc∙ 2)
X ⦉ suc n ⦊ = fiber∙ {A = X ⦉ n ⦊} (trunc∙ (3 + n))

ConnCovEqFiberZero : (X : Pointed ℓ)
  → (X ⦉ 0 ⦊) ≡ (fiber∙ {A = X} (trunc∙ 2))
ConnCovEqFiberZero X = refl

ConnCovEqFiberConnCov : (X : Pointed ℓ) (n : ℕ)
  → (X ⦉ (suc n) ⦊) ≡ (fiber∙ {A = X ⦉ n ⦊} (trunc∙ (3 + n)))
ConnCovEqFiberConnCov X n = refl


ConnCovEqFiberConnCovTypZero : (X : Pointed ℓ)
  → typ (X ⦉ 0 ⦊) ≡ typ (fiber∙ {A = X} (trunc∙ 2))
ConnCovEqFiberConnCovTypZero X = refl

ConnCovEqFiberConnCovTyp : (X : Pointed ℓ) (n : ℕ)
  → typ (X ⦉ (suc n) ⦊) ≡ typ (fiber∙ {A = X ⦉ n ⦊} (trunc∙ (3 + n)))
ConnCovEqFiberConnCovTyp X n = refl


ConnCovIsConn : (X : Pointed ℓ) (n : ℕ)
  → isConnected (2 + n) (typ (X ⦉ n ⦊))
ConnCovIsConn X zero = truncIsConnected X 2 (trunc {X = X} 2 (pt X))
ConnCovIsConn X (suc n) =
  truncIsConnected (X ⦉ n ⦊) (3 + n) (trunc {X = X ⦉ n ⦊} (3 + n) (pt (X ⦉ n ⦊)))

-- despite some planning, this is still a mess!
ConnCovEqFiber : (X : Pointed ℓ) (n : ℕ) →
  (X ⦉ n ⦊) ≡ (fiber∙ {A = X} (trunc∙ (2 + n)))
ConnCovEqFiber X zero = ConnCovEqFiberZero X
ConnCovEqFiber X (suc n) = ConnCovEqFiberConnCov X n ∙
  ua∙' (fiber∙ (trunc∙ (3 + n))) (fiber∙ (trunc∙ (3 + n)))
  (fiber∙ (trunc∙ (3 + n))
 ≃∙⟨ ΣFamBaseChange (X ⦉ n ⦊) (fiber∙ {A = X} (trunc∙ (2 + n)))
     ( hLevelTrunc∙ (3 + n)) ( λ A → trunc∙ (3 + n))
     ( au∙ (X ⦉ n ⦊) (fiber∙ {A = X} (trunc∙ (2 + n)))
     ( ConnCovEqFiber X n)) ⟩
  (Σ (typ (fiber∙ {A = X} (trunc∙ (2 + n))))
  (truncFam (3 + n) {A* = fiber∙ {A = X} (trunc∙ (2 + n))}) ,
  (pt X , refl) , refl)
 ≃∙⟨ ΣAssoc∙ X (λ x → trunc {X = X} (2 + n) x ≡ trunc {X = X} (2 + n) (pt X))
     (λ x p →
     trunc {X = fiber∙ {A = X} (trunc∙ (2 + n))} (3 + n) (x , p)
     ≡ trunc {X = fiber∙ {A = X} (trunc∙ (2 + n))} (3 + n) (pt X , refl))
     refl refl ⟩
  (Σ (typ X) (λ x →
  Σ[ p ∈ trunc {X = X} (2 + n) x ≡ trunc {X = X} (2 + n) (pt X) ]
   trunc {X = fiber∙ {A = X} (trunc∙ (2 + n))} (3 + n) (x , p)
   ≡ trunc {X = fiber∙ {A = X} (trunc∙ (2 + n))} (3 + n) (pt X , refl))) ,
   pt X , refl , refl
 ≃∙⟨ ΣPtdFibEq X
     (λ x → Σ[ p ∈ trunc {X = X} (2 + n) x ≡ trunc {X = X} (2 + n) (pt X) ]
             trunc {X = fiber∙ {A = X} (trunc∙ (2 + n))} (3 + n) (x , p)
           ≡ trunc {X = fiber∙ {A = X} (trunc∙ (2 + n))} (3 + n) (pt X , refl))
     (λ x → Σ[ p ∈ trunc {X = X} (2 + n) x ≡ trunc {X = X} (2 + n) (pt X) ]
             hLevelTrunc (2 + n) ((x , p) ≡ (pt X , refl)))
     (refl , refl) (refl , ∣ refl ∣ₕ)
     (λ x →
       Σ-cong-equiv-snd (λ p → isoToEquiv (PathIdTruncIso (2 + n))))
     (ΣPathP (refl , (cong ∣_∣ (transportRefl refl)))) ⟩
  (Σ (typ X) (λ x →
  Σ[ p ∈ trunc {X = X} (2 + n) x ≡ trunc {X = X} (2 + n) (pt X) ]
  hLevelTrunc (2 + n) ((x , p)
                     ≡ (pt X , refl {x = trunc {X = X} (2 + n) (pt X)})))) ,
  (pt X , refl ,
  trunc {X = ((pt X , refl) ≡ (pt X , refl)) , refl} (2 + n) refl)
 ≃∙⟨ ΣPtdFibEq X
     (λ x → Σ[ p ∈ trunc {X = X} (2 + n) x ≡ trunc {X = X} (2 + n) (pt X) ]
     hLevelTrunc (2 + n)
     ((x , p) ≡ (pt X , refl {x = trunc {X = X} (2 + n) (pt X)})))
     (λ x → hLevelTrunc (2 + n)
     (Σ[ p ∈ trunc {X = X} (2 + n) x ≡ trunc {X = X} (2 + n) (pt X) ]
     hLevelTrunc (2 + n)
     ((x , p) ≡ (pt X , refl {x = trunc {X = X} (2 + n) (pt X)}))))
     (refl , ∣ refl ∣ₕ)
     ∣ refl , ∣ refl ∣ₕ ∣ₕ 
     (λ x → invEquiv (truncIdempotent≃ (2 + n)
     (isOfHLevelΣ (2 + n) (isOfHLevelSuc (suc n)
                          (isOfHLevelPath' (suc n)
                          (isOfHLevelTrunc (2 + n)) _ _))
       λ p → isOfHLevelTrunc (2 + n))))
     refl ⟩
  (Σ (typ X) (λ x → hLevelTrunc (2 + n)
  (Σ[ p ∈ trunc {X = X} (2 + n) x ≡ trunc {X = X} (2 + n) (pt X) ]
  hLevelTrunc (2 + n)
  (((x , p) ≡ (pt X , refl {x = trunc {X = X} (2 + n) (pt X)})))))) ,
  pt X , ∣ refl , ∣ refl ∣ₕ ∣ₕ
 ≃∙⟨ ΣPtdFibEq
     X
     (λ x → hLevelTrunc (2 + n)
     (Σ[ p ∈ trunc {X = X} (2 + n) x ≡ trunc {X = X} (2 + n) (pt X) ]
     hLevelTrunc (2 + n)
     (((x , p) ≡ (pt X , refl {x = trunc {X = X} (2 + n) (pt X)})))))
     (λ x → hLevelTrunc (2 + n)
     (Σ[ p ∈ trunc {X = X} (2 + n) x ≡ trunc {X = X} (2 + n) (pt X) ]
     (((x , p) ≡ (pt X , refl {x = trunc {X = X} (2 + n) (pt X)})))))
     ∣ refl , ∣ refl ∣ₕ ∣ₕ
     ∣ refl , refl ∣ₕ
     (λ x → invEquiv (isoToEquiv (truncOfΣIso (2 + n))))
     refl ⟩
  (Σ (typ X) (λ x → hLevelTrunc (2 + n)
  (Σ[ p ∈ trunc {X = X} (2 + n) x ≡ trunc {X = X} (2 + n) (pt X) ]
  ((x , p) ≡ (pt X , refl {x = trunc {X = X} (2 + n) (pt X)}))))) ,
  pt X , ∣ refl , refl ∣ₕ
 ≃∙⟨ ΣPtdFibEq X
     (λ x → hLevelTrunc (2 + n)
     (Σ[ p ∈ trunc {X = X} (2 + n) x ≡ trunc {X = X} (2 + n) (pt X) ]
     ((x , p) ≡ (pt X , refl {x = trunc {X = X} (2 + n) (pt X)}))))
     (λ x → hLevelTrunc (2 + n)
     (Σ[ p ∈ trunc {X = X} (2 + n) x ≡ trunc {X = X} (2 + n) (pt X) ]
      (Σ[ q ∈ x ≡ pt X ]
       PathP (λ i → trunc {X = X} (2 + n) (q i)
                   ≡ trunc {X = X} (2 + n) (pt X)) p refl)))
     ∣ refl , refl ∣ₕ ∣ refl , (refl , refl) ∣ₕ
     (λ x → cong≃ (hLevelTrunc (2 + n))
     (Σ-cong-equiv-snd (λ p →
     invEquiv ΣPathP≃PathPΣ)))
     (transportRefl ∣ refl , (refl , refl) ∣ₕ) ⟩
  (Σ (typ X) λ x → hLevelTrunc (2 + n)
  (Σ[ p ∈ trunc {X = X} (2 + n) x ≡ trunc {X = X} (2 + n) (pt X) ]
   (Σ[ q ∈ x ≡ pt X ]
    PathP (λ i → trunc {X = X} (2 + n) (q i)
                ≡ trunc {X = X} (2 + n) (pt X)) p refl))) ,
  (pt X) , ∣ refl , (refl , refl) ∣ₕ
 ≃∙⟨ ΣPtdFibEq X
     (λ x → hLevelTrunc (2 + n)
     (Σ[ p ∈ trunc {X = X} (2 + n) x ≡ trunc {X = X} (2 + n) (pt X) ]
      (Σ[ q ∈ x ≡ pt X ]
       PathP (λ i → trunc {X = X} (2 + n) (q i)
                   ≡ trunc {X = X} (2 + n) (pt X)) p refl)))
     (λ x → hLevelTrunc (2 + n)
     (Σ[ p ∈ trunc {X = X} (2 + n) x ≡ trunc {X = X} (2 + n) (pt X) ]
      (Σ[ q ∈ x ≡ pt X ]
       transport (λ i → trunc {X = X} (2 + n) (q i)
                       ≡ trunc {X = X} (2 + n) (pt X)) p ≡ refl)))
     ∣ refl , (refl , refl) ∣ₕ ∣ refl , (refl , fromPathP refl) ∣ₕ
     (λ x → cong≃ (hLevelTrunc (2 + n))
     (Σ-cong-equiv-snd (λ p →
     Σ-cong-equiv-snd (λ q →
     PathP≃Path (λ i → trunc {X = X} (2 + n) (q i)
                      ≡ trunc {X = X} (2 + n) (pt X)) p refl))))
     (transportRefl ∣ refl , (refl , fromPathP refl) ∣ₕ) ⟩
  (Σ (typ X) λ x → hLevelTrunc (2 + n)
  (Σ[ p ∈ trunc {X = X} (2 + n) x ≡ trunc {X = X} (2 + n) (pt X) ]
   (Σ[ q ∈ x ≡ pt X ]
    transport (λ i → trunc {X = X} (2 + n) (q i)
                    ≡ trunc {X = X} (2 + n) (pt X)) p ≡ refl))) ,
  (pt X) , ∣ refl , (refl , fromPathP refl) ∣ₕ
 ≃∙⟨ ΣPtdFibEq X
     (λ x → hLevelTrunc (2 + n)
     (Σ[ p ∈ trunc {X = X} (2 + n) x ≡ trunc {X = X} (2 + n) (pt X) ]
      (Σ[ q ∈ x ≡ pt X ]
       transport (λ i → trunc {X = X} (2 + n) (q i)
                       ≡ trunc {X = X} (2 + n) (pt X)) p ≡ refl)))
     (λ x → hLevelTrunc (2 + n)
     (Σ[ q ∈ x ≡ pt X ]
      (Σ[ p ∈ trunc {X = X} (2 + n) x ≡ trunc {X = X} (2 + n) (pt X) ]
       transport (λ i → trunc {X = X} (2 + n) (q i)
                       ≡ trunc {X = X} (2 + n) (pt X)) p ≡ refl)))
     ∣ refl , (refl , fromPathP refl) ∣ₕ
     ∣ refl , (refl , fromPathP refl) ∣ₕ
     (λ x → cong≃ (hLevelTrunc (2 + n))
       (ΣSwapNested (trunc {X = X} (2 + n) x ≡ trunc {X = X} (2 + n) (pt X))
        (x ≡ pt X) λ p q →
        transport (λ i → trunc {X = X} (2 + n) (q i)
                         ≡ trunc {X = X} (2 + n) (pt X)) p ≡ refl))
     (transportRefl ∣ refl , (refl , fromPathP refl) ∣ₕ) ⟩
  (Σ (typ X) λ x → hLevelTrunc (2 + n)
  ((Σ[ q ∈ x ≡ pt X ]
  (Σ[ p ∈ trunc {X = X} (2 + n) x ≡ trunc {X = X} (2 + n) (pt X) ]
  transport (λ i → trunc {X = X} (2 + n) (q i)
                  ≡ trunc {X = X} (2 + n) (pt X)) p ≡ refl)))) ,
  (pt X) , ∣ refl , (refl , fromPathP refl) ∣ₕ
 ≃∙⟨ ΣPtdFibEq X
     (λ x →
     hLevelTrunc (2 + n)
     ((Σ[ q ∈ x ≡ pt X ]
     (Σ[ p ∈ trunc {X = X} (2 + n) x ≡ trunc {X = X} (2 + n) (pt X) ]
     transport (λ i → trunc {X = X} (2 + n) (q i)
                     ≡ trunc {X = X} (2 + n) (pt X)) p ≡ refl))))
     (λ x → hLevelTrunc (2 + n) (x ≡ pt X))
     ∣ refl , (refl , fromPathP refl) ∣ₕ ∣ refl ∣ₕ
     (λ x → cong≃ (hLevelTrunc (2 + n))
     (Σ-contractSnd (transportOfPathPathContr X x (suc n) (2 + n))))
     (transportRefl ∣ refl ∣ₕ) ⟩
  (Σ (typ X) λ x → hLevelTrunc (2 + n) (x ≡ pt X)) , pt X , ∣ refl ∣ₕ
 ≃∙⟨ ΣPtdFibEq X
     (λ x → hLevelTrunc (2 + n) (x ≡ pt X))
     (λ x → trunc {X = X} (3 + n) x ≡ trunc {X = X} (3 + n) (pt X))
     ∣ refl ∣ₕ refl
     (λ x → invEquiv (isoToEquiv (PathIdTruncIso (2 + n)))) refl ⟩
  fiber∙ {A = X} (trunc∙ (3 + n)) ∎≃∙)


ConnCovFiberSeqZero : (X : Pointed ℓ)
  → FiberSeq (X ⦉ 0 ⦊) X (hLevelTrunc∙ 2 X)
ConnCovFiberSeqZero X =
  FiberEqFiberSeq ( fiber∙ {A = X} (trunc∙ 2)) (X ⦉ 0 ⦊) X (hLevelTrunc∙ 2 X)
                  ( ConnCovEqFiberZero X)
                  ( FiberFiberSeq X (hLevelTrunc∙ 2 X) (trunc∙ 2))


ConnCovFiberSeq : (X : Pointed ℓ) (n : ℕ)
  → FiberSeq (X ⦉ (suc n) ⦊) (X ⦉ n ⦊) (hLevelTrunc∙ (3 + n) (X ⦉ n ⦊))
ConnCovFiberSeq X n =
  FiberEqFiberSeq
  ( fiber∙ {A = X ⦉ n ⦊} (trunc∙ (3 + n)))
  ( X ⦉ (suc n) ⦊)
  ( X ⦉ n ⦊)
  ( hLevelTrunc∙ (3 + n) (X ⦉ n ⦊))
  ( ConnCovEqFiberConnCov X n)
  ( FiberFiberSeq (X ⦉ n ⦊)
  ( hLevelTrunc∙ (3 + n) (X ⦉ n ⦊))
  ( trunc∙ (3 + n)))

AlternativeFiberSeq : (X : Pointed ℓ) (n : ℕ)
   → FiberSeq (X ⦉ (suc n) ⦊) X (hLevelTrunc∙ (3 + n) X)
AlternativeFiberSeq X n =
  FiberEqFiberSeq
    ( fiber∙ {A = X} (trunc∙ (3 + n))) ( X ⦉ (suc n) ⦊)
    X ( hLevelTrunc∙ (3 + n) X)
    ( ConnCovEqFiber X (suc n) ⁻¹)
    ( FiberFiberSeq X (hLevelTrunc∙ (3 + n) X) (trunc∙ (3 + n)))


Conn→Eq≥ConnCov : (X : Pointed ℓ) (m n : ℕ) → m ≥ (2 + n)
  → isConnected m (typ X) → X ≡ (X ⦉ n ⦊)
Conn→Eq≥ConnCov X m zero (k , p) cX =
  ContrBase→TotalEqFib (X ⦉ 0 ⦊) X (hLevelTrunc∙ 2 X)
  ( isConnectedSubtr 2 k (transport (λ i → isConnected (p (~ i)) (typ X)) cX))
  ( ConnCovFiberSeqZero X) ⁻¹
Conn→Eq≥ConnCov X m (suc n) (k , p) cX =
  ContrBase→TotalEqFib (X ⦉ (suc n) ⦊) X (hLevelTrunc∙ (3 + n) X)
  ( isConnectedSubtr (3 + n) k
    ( transport (λ i → isConnected (p (~ i)) (typ X)) cX))
  ( AlternativeFiberSeq X n) ⁻¹


1ConnCovEq : (X : Pointed ℓ) (scX : isConnected 3 (typ X))
  → X ≡ (X ⦉ 1 ⦊)
1ConnCovEq X scX = Conn→Eq≥ConnCov X 3 1 (0 , refl) scX


Conn→Conn<ConnCov : (X : Pointed ℓ) (m n : ℕ) → (m < (2 + n))
  → isConnected m (typ X) → isConnected m (typ (X ⦉ n ⦊))
Conn→Conn<ConnCov X m n (k , k+m+1≡2+n) cX =
  isConnectedSubtr m (k + 1)
  ( transport
    ( λ i → isConnected ((((+-assoc k 1 m) ⁻¹) ∙ k+m+1≡2+n) (~ i))
    ( typ (X ⦉ n ⦊)))
    ( ConnCovIsConn X n))


Conn→Conn≥ConnCov : (X : Pointed ℓ) (m n : ℕ) → (m ≥ (2 + n))
  → isConnected m (typ X) → isConnected m (typ (X ⦉ n ⦊))
Conn→Conn≥ConnCov X m n hmn cX =
  transport (λ i → isConnected m (typ ((Conn→Eq≥ConnCov X m n hmn cX) i))) cX

≱→<Dec : (m n : ℕ) → ¬ m ≥ n → (Dec (m < n)) → m < n
≱→<Dec m n x (yes p) = p
≱→<Dec m n ¬m≥n (no ¬p) = <-asym' λ n<m+1 → ¬m≥n (<-asym' ¬p)

≱→< : (m n : ℕ) → ¬ m ≥ n → m < n
≱→< m n x = ≱→<Dec m n x (<Dec m n)


Conn→Dec≥→ConnConnCov : (X : Pointed ℓ) (m n : ℕ) → Dec (m ≥ (2 + n))
  → isConnected m (typ X) → isConnected m (typ (X ⦉ n ⦊))
Conn→Dec≥→ConnConnCov X m n (yes p) cX =
  Conn→Conn≥ConnCov X m n p cX
Conn→Dec≥→ConnConnCov X m n (no ¬p) cX =
  Conn→Conn<ConnCov X m n (≱→< m (2 + n) ¬p) cX


Conn→ConnConnCov : (X : Pointed ℓ) (m n : ℕ)
  → isConnected m (typ X) → isConnected m (typ (X ⦉ n ⦊))
Conn→ConnConnCov X m n = Conn→Dec≥→ConnConnCov X m n (≤Dec (2 + n) m)
