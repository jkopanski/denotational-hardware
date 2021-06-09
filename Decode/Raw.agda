{-# OPTIONS --safe --without-K #-}

open import Level

open import Categorical.Raw
open import Categorical.Equiv
open import Categorical.Laws as L hiding (Category)
open import Categorical.Homomorphism

module Decode.Raw {o} {obj : Set o}
                  {ℓ} (_↠_ : obj → obj → Set ℓ) ⦃ _ : Category _↠_ ⦄
                  q ⦃ _ : Equivalent q _↠_ ⦄
                  {o′} {obj′ : Set o′} (⟦_⟧ : obj′ → obj)
                  ⦃ _ : L.Category _↠_ q ⦄
 where

open import Decode.Type _↠_ q ⟦_⟧ public

module decode-raw-instances where

  instance

    category : Category _⇨_
    category = record
      { id = λ {a} → mk id id (
          begin
             d a ∘ id
           ≈⟨ identityʳ ⟩
             d a
           ≈˘⟨ identityˡ ⟩
             id ∘ d a
           ∎)
      ; _∘_ = λ {a b c} (mk g g′ spec-g) (mk f f′ spec-f) →
          mk (g ∘ f) (g′ ∘ f′) (
             begin
               d c ∘ (g′ ∘ f′)
             ≈˘⟨ assoc ⟩
               (d c ∘ g′) ∘ f′
             ≈⟨ ∘≈ˡ spec-g ⟩
               (g ∘ d b) ∘ f′
             ≈⟨ assoc ⟩
               g ∘ (d b ∘ f′)
             ≈⟨ ∘≈ʳ spec-f ⟩
               g ∘ (f ∘ d a)
             ≈˘⟨ assoc ⟩
               (g ∘ f) ∘ d a
             ∎)
      }
      where open D
            open ≈-Reasoning
    
  -- TODO: Cartesian
