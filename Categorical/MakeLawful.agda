{-# OPTIONS --safe --without-K #-}

-- Laws from homomorphisms. Given a homomorphism with lawful target, prove the
-- source to be lawful, assuming that source equivalence is defined
-- homomorphically.

module Categorical.MakeLawful where

open import Level using (Level)

open import Categorical.Raw
open import Categorical.Homomorphism
open import Categorical.Laws as L hiding (Category)

open ≈-Reasoning

private
  variable
    o ℓ o₁ ℓ₁ o₂ ℓ₂ : Level
    obj obj₁ obj₂ : Set o
    a b c : obj

LawfulCategoryᶠ : {obj₁ : Set o₁} {_⇨₁_ : obj₁ → obj₁ → Set ℓ₁}
                  {obj₂ : Set o₂} (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂)
                  {q : Level} ⦃ _ : Equivalent q _⇨₂_ ⦄
                  ⦃ _ : Category _⇨₁_ ⦄ ⦃ _ : Category _⇨₂_ ⦄
                  ⦃ _ : L.Category _⇨₂_ q ⦄
                  ⦃ _ : Homomorphismₒ obj₁ obj₂ ⦄
                  ⦃ H : Homomorphism _⇨₁_ _⇨₂_ ⦄
                  ⦃ F : CategoryH _⇨₁_ _⇨₂_ q ⦄
                → L.Category _⇨₁_ q ⦃ equiv = H-equiv H ⦄

LawfulCategoryᶠ F = record
  { identityˡ = λ {a b} {f} →
      begin
        Fₘ (id ∘ f)
      ≈⟨ F-∘ ⟩
        Fₘ id ∘ Fₘ f
      ≈⟨ ∘≈ˡ F-id  ⟩
        id ∘ Fₘ f
      ≈⟨ identityˡ ⟩
        Fₘ f
      ∎
  ; identityʳ = λ {a b} {f} →
      begin
        Fₘ (f ∘ id)
      ≈⟨ F-∘ ⟩
        Fₘ f ∘ Fₘ id
      ≈⟨ ∘≈ʳ F-id  ⟩
        Fₘ f ∘ id
      ≈⟨ identityʳ ⟩
        Fₘ f
      ∎
  ; assoc = λ {a b c d} {f g h} →
      begin
        Fₘ ((h ∘ g) ∘ f)
      ≈⟨ F-∘ ⟩
        Fₘ (h ∘ g) ∘ Fₘ f
      ≈⟨ ∘≈ˡ F-∘ ⟩
        (Fₘ h ∘ Fₘ g) ∘ Fₘ f
      ≈⟨ assoc ⟩
        Fₘ h ∘ (Fₘ g ∘ Fₘ f)
      ≈˘⟨ ∘≈ʳ F-∘ ⟩
        Fₘ h ∘ (Fₘ (g ∘ f))
      ≈˘⟨ F-∘ ⟩
        Fₘ (h ∘ (g ∘ f))
      ∎
  ; ∘≈ = λ {a b c}{f g h k} h∼k f∼g →
      begin
        Fₘ (h ∘ f)
      ≈⟨ F-∘ ⟩
        Fₘ h ∘ Fₘ f
      ≈⟨ ∘≈ h∼k f∼g ⟩
        Fₘ k ∘ Fₘ g
      ≈˘⟨ F-∘ ⟩
        Fₘ (k ∘ g)
      ∎
  }

-- TODO: Cartesian, etc.

