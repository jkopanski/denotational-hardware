{-# OPTIONS --safe --without-K #-}

open import Categorical.Raw
open import Categorical.Equiv
open import Categorical.Laws as L hiding (Category)
open import Categorical.Homomorphism

module Encode.Raw {o} {obj : Set o}
                  {ℓ} (_↠_ : obj → obj → Set ℓ) ⦃ _ : Category _↠_ ⦄
                  q ⦃ _ : Equivalent q _↠_ ⦄
                  {o′} {obj′ : Set o′} (⟦_⟧ : obj′ → obj)
                  ⦃ _ : L.Category _↠_ q ⦄
 where

open import Encode.Type _↠_ q ⟦_⟧ public

module decode-raw-instances where

  instance

    category : Category _⇨_
    category = record
      { id = λ {a} → mk id id
          (begin
             e a ∘ id
           ≈⟨ identityʳ ⟩
             e a
           ≈˘⟨ identityˡ ⟩
             id ∘ e a
           ∎)
      ; _∘_ = λ {a b c} (mk g g′ spec-g) (mk f f′ spec-f) →
          mk (g ∘ f) (g′ ∘ f′)
            (begin
               e c ∘ (g ∘ f)
             ≈˘⟨ assoc ⟩
               (e c ∘ g) ∘ f
             ≈⟨ ∘≈ˡ spec-g ⟩
               (g′ ∘ e b) ∘ f
             ≈⟨ assoc ⟩
               g′ ∘ (e b ∘ f)
             ≈⟨ ∘≈ʳ spec-f ⟩
               g′ ∘ (f′ ∘ e a)
             ≈˘⟨ assoc ⟩
               (g′ ∘ f′) ∘ e a
             ∎)
      }
      where open D
            open ≈-Reasoning
    
  -- TODO: Cartesian, CartesianClosed, and Logic.
