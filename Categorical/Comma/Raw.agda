{-# OPTIONS --safe --without-K #-}

open import Level

open import Categorical.Raw
open import Categorical.Equiv
open import Categorical.Laws as L hiding (Category)
open import Categorical.Homomorphism

module Categorical.Comma.Raw
   {o₁}{obj₁ : Set o₁} {ℓ₁}(_⇨₁_ : obj₁ → obj₁ → Set ℓ₁) ⦃ _ : Category _⇨₁_ ⦄
   {o₂}{obj₂ : Set o₂} {ℓ₂}(_⇨₂_ : obj₂ → obj₂ → Set ℓ₂) ⦃ _ : Category _⇨₂_ ⦄
   {o₃}{obj₃ : Set o₃} {ℓ₃}(_⇨₃_ : obj₃ → obj₃ → Set ℓ₃) ⦃ _ : Category _⇨₃_ ⦄
   q ⦃ _ : Equivalent q _⇨₃_ ⦄ ⦃ _ : L.Category _⇨₃_ q ⦄
   ⦃ _ : Homomorphismₒ obj₁ obj₃ ⦄ ⦃ _ : Homomorphism _⇨₁_ _⇨₃_ ⦄
     ⦃ _ : CategoryH _⇨₁_ _⇨₃_ q ⦄
   ⦃ _ : Homomorphismₒ obj₂ obj₃ ⦄ ⦃ _ : Homomorphism _⇨₂_ _⇨₃_ ⦄
     ⦃ _ : CategoryH _⇨₂_ _⇨₃_ q ⦄
 where

open import Categorical.Comma.Type _⇨₁_ _⇨₂_ _⇨₃_ q public

module comma-raw-instances where

  instance
    open Obj
    open ≈-Reasoning
  
    category : Category _⇨_
    category = record
      { id  = λ {a} → mk id id
          (begin
             Fₘ id ∘ h a
           ≈⟨ ∘≈ˡ F-id ⟩
             id ∘ h a
           ≈⟨ identityˡ ⟩
             h a
           ≈˘⟨ identityʳ ⟩
             h a ∘ id
           ≈˘⟨ ∘≈ʳ F-id ⟩
             h a ∘ Fₘ id
           ∎)
      ; _∘_ = λ {a b c} (mk g₁ g₂ comm-g) (mk f₁ f₂ comm-f) →
          mk (g₁ ∘ f₁) (g₂ ∘ f₂)
           (begin
              Fₘ (g₂ ∘ f₂) ∘ h a
            ≈⟨ ∘≈ˡ F-∘ ⟩
              (Fₘ g₂ ∘ Fₘ f₂) ∘ h a
            ≈⟨ assoc ⟩
              Fₘ g₂ ∘ (Fₘ f₂ ∘ h a)
            ≈⟨ ∘≈ʳ comm-f ⟩
              Fₘ g₂ ∘ (h b ∘ Fₘ f₁)
            ≈˘⟨ assoc ⟩
              (Fₘ g₂ ∘ h b) ∘ Fₘ f₁
            ≈⟨ ∘≈ˡ comm-g ⟩
              (h c ∘ Fₘ g₁) ∘ Fₘ f₁
            ≈⟨ assoc ⟩
              h c ∘ (Fₘ g₁ ∘ Fₘ f₁)
            ≈˘⟨ ∘≈ʳ F-∘ ⟩
              h c ∘ Fₘ (g₁ ∘ f₁)
            ∎)
      }

  -- TODO: Cartesian, CartesianClosed, and Logic.
