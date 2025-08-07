module Pullback.IsPPullback where

open import Everything

open import Pullback.IsPullback

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

private
  variable
    ℓ : Level

_▹∙_ : {A : Pointed ℓ} {B : Pointed ℓ} {C : Pointed ℓ} {f f' : B →∙ C}
      (α : f ≡ f')
      (g : A →∙ B) → f ∘∙ g ≡ f' ∘∙ g
α ▹∙ g = cong (_∘∙ g) α

module _ {B C D : Pointed ℓ} (f : B →∙ D) (g : C →∙ D) where
  SpanConeOn∙ : Pointed ℓ → Type ℓ
  SpanConeOn∙ A = Σ[ g' ∈ (A →∙ B) ] Σ[ f' ∈ (A →∙ C) ] f ∘∙ g' ≡ g ∘∙ f'

  precomp∙ : {A A' : Pointed ℓ} → (A' →∙ A) → SpanConeOn∙ A → SpanConeOn∙ A'
  fst (precomp∙ h sco) = (fst sco) ∘∙ h
  fst (snd (precomp∙ h sco)) = (fst (snd sco)) ∘∙ h
  snd (snd (precomp∙ h sco)) = (∘∙-assoc f (fst sco) h) ⁻¹
                              ∙ (snd (snd sco) ▹∙ h)
                              ∙ ∘∙-assoc g (fst (snd sco)) h

  module isPullback∙ {P : Pointed ℓ} (g' : P →∙ B) (f' : P →∙ C) (α : f ∘∙ g' ≡ g ∘∙ f') where
    pullbackComparison∙ : (E : Pointed ℓ) → (E →∙ P) → SpanConeOn∙ E
    pullbackComparison∙ E h = precomp∙ h (g' , f' , α)

    record isPullback∙ : Type (ℓ-suc ℓ) where
      no-eta-equality
      field
        comparisonIsEquiv∙ : (E : Pointed ℓ) → isEquiv (pullbackComparison∙ E)
      

module _ {B C D : Pointed ℓ} (f : B →∙ D) (g : C →∙ D)
         {P : Type ℓ} (g' : P → (typ B)) (f' : P → (typ C))
         (α : (fst f) ∘ g' ≡ (fst g) ∘ f')
         where

         open isPullback (fst f) (fst g) g' f' α

         module pullback→pullback∙ (pbP : isPullback) where
          

           postulate
             pb-pt : P

             proj1-pt : g' pb-pt ≡ (pt B)

             proj2-pt : f' pb-pt ≡ (pt C)

             α' : f ∘∙ (g' , proj1-pt) ≡ (g ∘∙ (f' , proj2-pt))

           open isPullback∙ f g (g' , proj1-pt) (f' , proj2-pt) α'

           postulate
             pbP' : isPullback∙
           
