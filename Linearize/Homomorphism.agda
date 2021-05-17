{-# OPTIONS --safe --without-K #-}

open import Categorical.Equiv
open import Categorical.Raw

module Linearize.Homomorphism {ℓₘ}{objₘ : Set ℓₘ} ⦃ _ : Products objₘ ⦄
             (_⇨ₘ_ : objₘ → objₘ → Set ℓₘ) (let infix 0 _⇨ₘ_; _⇨ₘ_ = _⇨ₘ_)
             {ℓ}{obj : Set ℓ} ⦃ _ : Products obj ⦄
             (_⇨ₚ_ : obj → obj → Set ℓ) (let infix 0 _⇨ₚ_; _⇨ₚ_ = _⇨ₚ_)
             (_⇨ᵣ_ : obj → obj → Set ℓ) (let infix 0 _⇨ᵣ_; _⇨ᵣ_ = _⇨ᵣ_)
             ⦃ Hₒ : Homomorphismₒ obj objₘ ⦄
             ⦃ _ : Cartesian _⇨ₘ_ ⦄          -- monoidal suffices
             ⦃ _ : Cartesian _⇨ᵣ_ ⦄          -- braided suffices
             ⦃ Hₚ : Homomorphism _⇨ₚ_ _⇨ₘ_ ⦄
             ⦃ Hᵣ : Homomorphism _⇨ᵣ_ _⇨ₘ_ ⦄
             ⦃ _ : ProductsH obj _⇨ₘ_ ⦄
             q ⦃ _ : Equivalent q _⇨ₘ_ ⦄
             ⦃ _ : CategoryH _⇨ᵣ_ _⇨ₘ_ q ⦄
  where

private variable a b c d : obj

open import Linearize.Raw _⇨ₘ_ _⇨ₚ_ _⇨ᵣ_ public

⟦_⟧ₖ : (a ⇨ b) → (Fₒ a ⇨ₘ Fₒ b)
⟦ ⌞ r ⌟ ⟧ₖ = Fₘ r
⟦ f ∘·first p ∘ r ⟧ₖ = ⟦ f ⟧ₖ ∘ μ ∘ first (Fₘ p) ∘ μ⁻¹ ∘ Fₘ r

{-
private

  open ≈-Reasoning

  open Homomorphism Hₚ using () renaming (Fₘ to ⟦_⟧ₚ)
  open Homomorphism Hᵣ using () renaming (Fₘ to ⟦_⟧ᵣ)

  infixr 9 _⟦∘⟧_
  _⟦∘⟧_ : ∀ (g : b ⇨ c) (f : a ⇨ b) → ⟦ g ∘ f ⟧ₖ ≈ ⟦ g ⟧ₖ ∘ ⟦ f ⟧ₖ

  g ⟦∘⟧ (f ∘·first p ∘ r) =
    begin
      ⟦ g ∘ (f ∘·first p ∘ r) ⟧ₖ
    ≡⟨⟩
      ⟦ (g ∘ f) ∘·first p ∘ r ⟧ₖ
    ≡⟨⟩
      ⟦ g ∘ f ⟧ₖ ∘ μ ∘ first ⟦ p ⟧ₚ ∘ μ⁻¹ ∘ ⟦ r ⟧ᵣ
    ≈⟨ ∘≈ˡ (g ⟦∘⟧ f) ⟩
      (⟦ g ⟧ₖ ∘ ⟦ f ⟧ₖ) ∘ μ ∘ first ⟦ p ⟧ₚ ∘ μ⁻¹ ∘ ⟦ r ⟧ᵣ
    ≈⟨ assoc ⟩
      ⟦ g ⟧ₖ ∘ ⟦ f ⟧ₖ ∘ μ ∘ first ⟦ p ⟧ₚ ∘ μ⁻¹ ∘ ⟦ r ⟧ᵣ
    ≡⟨⟩
      ⟦ g ⟧ₖ ∘ ⟦ f ∘·first p ∘ r ⟧ₖ
    ∎

  (g ∘·first p ∘ r₂) ⟦∘⟧ ⌞ r₁ ⌟ =
    begin
      ⟦ (g ∘·first p ∘ r₂) ∘ ⌞ r₁ ⌟ ⟧ₖ
    ≡⟨⟩
      ⟦ g ∘·first p ∘ (r₂ ∘ r₁) ⟧ₖ
    ≡⟨⟩
      ⟦ g ⟧ₖ ∘ μ ∘ first ⟦ p ⟧ₚ ∘ μ⁻¹ ∘ ⟦ r₂ ∘ r₁ ⟧ᵣ
    ≈⟨ ∘≈ʳ (∘≈ʳ (∘≈ʳ (∘≈ʳ (F-∘ r₂ r₁)))) ⟩
      ⟦ g ⟧ₖ ∘ μ ∘ first ⟦ p ⟧ₚ ∘ μ⁻¹ ∘ ⟦ r₂ ⟧ᵣ ∘ ⟦ r₁ ⟧ᵣ
    ≈˘⟨ assoc⁵ ⟩
      (⟦ g ⟧ₖ ∘ μ ∘ first ⟦ p ⟧ₚ ∘ μ⁻¹ ∘ ⟦ r₂ ⟧ᵣ) ∘ ⟦ r₁ ⟧ᵣ
    ≡⟨⟩
      ⟦ g ∘·first p ∘ r₂ ⟧ₖ ∘ ⟦ ⌞ r₁ ⌟ ⟧ₖ
    ∎

  ⌞ r₂ ⌟ ⟦∘⟧ ⌞ r₁ ⌟ = F-∘ r₂ r₁
-}

module linearize-homomorphism-instances where

  instance

    homomorphism : Homomorphism _⇨_ _⇨ₘ_
    homomorphism = record { Fₘ = ⟦_⟧ₖ }

    -- categoryH : CategoryH _⇨_ _⇨ₘ_ q
    -- categoryH = ?

    -- cartesianH : CartesianH _⇨_ _⇨ₘ_ q
    -- cartesianH = ?
