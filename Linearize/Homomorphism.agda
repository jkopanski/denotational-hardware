{-# OPTIONS --safe --without-K #-}

open import Categorical.Homomorphism
open import Categorical.Laws as L hiding (Category; Cartesian; CartesianClosed)

module Linearize.Homomorphism {o}{objₘ : Set o} ⦃ _ : Products objₘ ⦄ ⦃ _ : Exponentials objₘ ⦄
             {ℓₘ}(_⇨ₘ_ : objₘ → objₘ → Set ℓₘ) -- (let infix 0 _⇨ₘ_; _⇨ₘ_ = _⇨ₘ_)
             {ℓ}{obj : Set ℓ} ⦃ _ : Products obj ⦄ ⦃ _ : Exponentials obj ⦄
             (_⇨ₚ_ : obj → obj → Set ℓ) -- (let infix 0 _⇨ₚ_; _⇨ₚ_ = _⇨ₚ_)
             (_⇨ᵣ_ : obj → obj → Set ℓ) -- (let infix 0 _⇨ᵣ_; _⇨ᵣ_ = _⇨ᵣ_)
             ⦃ _ : Category _⇨ₘ_ ⦄ ⦃ _ : Cartesian _⇨ₘ_ ⦄
               ⦃ _ : CartesianClosed _⇨ₘ_ ⦄   -- monoidal suffices?
             ⦃ _ : Category _⇨ᵣ_ ⦄ ⦃ _ : Cartesian _⇨ᵣ_ ⦄  -- braided suffices?
             -- The rest are for ⟦_⟧ₖ. Maybe move them into a submodule.
             ⦃ Hₒ : Homomorphismₒ obj objₘ ⦄
             ⦃ Hₚ : Homomorphism _⇨ₚ_ _⇨ₘ_ ⦄
             ⦃ Hᵣ : Homomorphism _⇨ᵣ_ _⇨ₘ_ ⦄
             {q} ⦃ _ : Equivalent q _⇨ₘ_ ⦄
             ⦃ _ : ProductsH obj _⇨ₘ_ ⦄ ⦃ _ : ExponentialsH obj _⇨ₘ_ ⦄
             ⦃ _ : L.Category _⇨ₘ_ ⦄ ⦃ _ : CategoryH _⇨ᵣ_ _⇨ₘ_ ⦄
             -- Maybe move into sub-module:
             ⦃ _ : L.Cartesian _⇨ₘ_ ⦄ ⦃ _ : CartesianH _⇨ᵣ_ _⇨ₘ_ ⦄
  where


open import Functions.Raw

open import Linearize.Raw _⇨ₘ_ _⇨ₚ_ _⇨ᵣ_ public

-- TODO:

private

  variable a b c d : obj

  open ≈-Reasoning
  open import Categorical.Reasoning

  -- Disambiguators
  Fᵣ : (a ⇨ᵣ b) → (Fₒ a ⇨ₘ Fₒ b)
  Fᵣ = Fₘ
  Fₚ : (a ⇨ₚ b) → (Fₒ a ⇨ₘ Fₒ b)
  Fₚ = Fₘ

  infixr 9 _⟦∘⟧_
  _⟦∘⟧_ : ∀ (g : b ⇨ c) (f : a ⇨ b) → ⟦ g ∘ f ⟧ₖ ≈ ⟦ g ⟧ₖ ∘ ⟦ f ⟧ₖ

  -- g ⟦∘⟧ (f ∘·first p ∘ r) =
  --   begin
  --     ⟦ g ∘ (f ∘·first p ∘ r) ⟧ₖ
  --   ≡⟨⟩
  --     ⟦ (g ∘ f) ∘·first p ∘ r ⟧ₖ
  --   ≡⟨⟩
  --     ⟦ g ∘ f ⟧ₖ ∘ μ ∘ first (Fₘ p) ∘ μ⁻¹ ∘ Fₘ r
  --   ≈⟨ ∘≈ˡ (g ⟦∘⟧ f) ⟩
  --     (⟦ g ⟧ₖ ∘ ⟦ f ⟧ₖ) ∘ μ ∘ first (Fₘ p) ∘ μ⁻¹ ∘ Fₘ r
  --   ≈⟨ ∘-assocʳ ⟩
  --     ⟦ g ⟧ₖ ∘ ⟦ f ⟧ₖ ∘ μ ∘ first (Fₘ p) ∘ μ⁻¹ ∘ Fₘ r
  --   ≡⟨⟩
  --     ⟦ g ⟧ₖ ∘ ⟦ f ∘·first p ∘ r ⟧ₖ
  --   ∎

  g ⟦∘⟧ (f ∘·first p ∘ r) = ∘≈ˡ (g ⟦∘⟧ f) ; ∘-assocʳ

  -- (g ∘·first p ∘ r₂) ⟦∘⟧ ⌞ r₁ ⌟ =
  --   begin
  --     ⟦ (g ∘·first p ∘ r₂) ∘ ⌞ r₁ ⌟ ⟧ₖ
  --   ≡⟨⟩
  --     ⟦ g ∘·first p ∘ (r₂ ∘ r₁) ⟧ₖ
  --   ≡⟨⟩
  --     ⟦ g ⟧ₖ ∘ μ ∘ first (Fₘ p) ∘ μ⁻¹ ∘ Fₘ (r₂ ∘ r₁)
  --   ≈⟨ ∘≈ʳ (∘≈ʳ (∘≈ʳ (∘≈ʳ F-∘))) ⟩
  --     ⟦ g ⟧ₖ ∘ μ ∘ first (Fₘ p) ∘ μ⁻¹ ∘ Fₘ r₂ ∘ Fₘ r₁
  --   ≈⟨ ∘-assocˡ⁵ ⟩
  --     (⟦ g ⟧ₖ ∘ μ ∘ first (Fₘ p) ∘ μ⁻¹ ∘ Fₘ r₂) ∘ Fₘ r₁
  --   ≡⟨⟩
  --     ⟦ g ∘·first p ∘ r₂ ⟧ₖ ∘ ⟦ ⌞ r₁ ⌟ ⟧ₖ
  --   ∎

  (g ∘·first p ∘ r₂) ⟦∘⟧ ⌞ r₁ ⌟ = ∘≈ʳ (∘≈ʳ (∘≈ʳ (∘≈ʳ F-∘))) ; ∘-assocˡ⁵

  ⌞ r₂ ⌟ ⟦∘⟧ ⌞ r₁ ⌟ = F-∘

  -- Fₘ (first {b = b} f) ∘ μ ≈ μ ∘ first (Fₘ f)

  ⟦first⟧′ : {b : obj} (f : a ⇨ c) → ⟦ firstₖ {b = b} f ⟧ₖ ≈ μ ∘ first ⟦ f ⟧ₖ ∘ μ⁻¹
  ⟦first⟧′ ⌞ r ⌟ = F-first′

  -- ⟦first⟧′ {b = b} ⌞ r ⌟ =
  --   begin
  --     ⟦ firstₖ ⌞ r ⌟ ⟧ₖ
  --   ≡⟨⟩
  --     ⟦ ⌞ first r ⌟ ⟧ₖ
  --   ≡⟨⟩
  --     Fₘ (first r)
  --   ≈⟨ F-first′ ⟩
  --     μ ∘ first (Fₘ r) ∘ μ⁻¹
  --   ≡⟨⟩
  --     μ ∘ first ⟦ ⌞ r ⌟ ⟧ₖ ∘ μ⁻¹
  --   ∎

  ⟦first⟧′ (f ∘·first p ∘ r) =
    begin
      ⟦ firstₖ (f ∘·first p ∘ r) ⟧ₖ
    ≡⟨⟩
      ⟦ (firstₖ f ∘ ⌞ assocˡ ⌟) ∘·first p ∘ (assocʳ ∘ first r) ⟧ₖ
    ≡⟨⟩
      ⟦ firstₖ f ∘ ⌞ assocˡ ⌟ ⟧ₖ ∘ μ ∘ first (Fₚ p) ∘ μ⁻¹ ∘ Fᵣ (assocʳ ∘ first r)

    -- ≈⟨ ∘-assocʳ⁵ ⟩
    --   ⟦ firstₖ f ∘ ⌞ assocˡ ⌟ ⟧ₖ ∘ μ ∘ first (Fₚ p) ∘ μ⁻¹ ∘ Fᵣ (assocʳ ∘ first r) ∘ μ
    -- ≈⟨ ∘≈ˡ (firstₖ f ⟦∘⟧ ⌞ assocˡ ⌟) ⟩
    --   (⟦ firstₖ f ⟧ₖ ∘ ⟦ ⌞ assocˡ ⌟ ⟧ₖ) ∘ μ ∘ first (Fₚ p) ∘ μ⁻¹ ∘ Fᵣ (assocʳ ∘ first r) ∘ μ
    -- ≈⟨ ∘≈ʳ (∘≈ʳ (∘≈ʳ (∘≈ʳ (∘≈ˡ F-∘)))) ⟩
    --   (⟦ firstₖ f ⟧ₖ ∘ ⟦ ⌞ assocˡ ⌟ ⟧ₖ) ∘ μ ∘ first (Fₚ p) ∘ μ⁻¹ ∘ (Fᵣ assocʳ ∘ Fᵣ (first r)) ∘ μ
    -- ≈⟨ (∘≈ʳ (∘≈ʳ (∘≈ʳ (∘≈ʳ ∘-assocʳ))) ; ∘-assocʳ) ⟩
    --   ⟦ firstₖ f ⟧ₖ ∘ Fᵣ assocˡ ∘ μ ∘ first (Fₚ p) ∘ μ⁻¹ ∘ Fᵣ assocʳ ∘ Fᵣ (first r) ∘ μ
    -- ≈⟨ ∘≈ʳ (∘≈ʳ (∘≈ʳ (∘≈ʳ (∘≈ʳ (∘≈ʳ F-first))))) ⟩

      -- ⟦ firstₖ f ⟧ₖ ∘ Fᵣ assocˡ ∘ μ ∘ first (Fₚ p) ∘ μ⁻¹ ∘ Fᵣ assocʳ ∘ μ ∘ first (Fᵣ r)

    -- ≈⟨ {!∘≈ˡ ?!} ⟩
    --   (μ ∘ first ⟦ f ⟧ₖ) ∘ ⟦ ⌞ assocˡ ⌟ ⟧ₖ ∘ μ ∘ first (Fₚ p) ∘ μ⁻¹ ∘ Fᵣ assocʳ ∘ Fᵣ (first r) ∘ μ

    -- ≈⟨ {!!} ⟩
    --   μ ∘ first ⟦ f ⟧ₖ ∘ first μ ∘ assocˡ ∘ first (Fₚ p) ∘ assocʳ ∘ first μ⁻¹ ∘ first (Fᵣ r)
    -- ≈⟨ ∘≈ʳ (∘≈ʳ (∘≈ʳ ∘-assocˡ³)) ⟩
    --   μ ∘ first ⟦ f ⟧ₖ ∘ first μ ∘ (assocˡ ∘ first (Fₚ p) ∘ assocʳ) ∘ first μ⁻¹ ∘ first (Fᵣ r)
    -- ≈⟨ ∘≈ʳ (∘≈ʳ (∘≈ʳ (∘≈ˡ (sym first-first)))) ⟩
    --   μ ∘ first ⟦ f ⟧ₖ ∘ first μ ∘ first (first (Fₚ p)) ∘ first μ⁻¹ ∘ first (Fᵣ r)
    -- ≈⟨ ∘≈ʳ (∘≈ʳ (∘≈ʳ (∘≈ʳ first∘⊗ ; first∘⊗) ; first∘⊗) ; first∘⊗) ⟩
    --   μ ∘ first (⟦ f ⟧ₖ ∘ μ ∘ first (Fₚ p) ∘ μ⁻¹ ∘ Fᵣ r)
    -- ≡⟨⟩

    ≈⟨ {!!} ⟩
      μ ∘ first ⟦ f ∘·first p ∘ r ⟧ₖ ∘ μ⁻¹
    ∎



  -- -- ⟦first⟧ (f ∘·first p ∘ r) =
  -- --   begin
  -- --     ⟦ firstₖ (f ∘·first p ∘ r) ⟧ₖ
  -- --   ≡⟨⟩
  -- --     ⟦ (firstₖ f ∘ ⌞ assocˡ ⌟) ∘·first p ∘ (assocʳ ∘ first r) ⟧ₖ
  -- --   ≡⟨⟩
  -- --     ⟦ firstₖ f ∘ ⌞ assocˡ ⌟ ⟧ₖ ∘ first (Fₘ p) ∘ Fₘ (assocʳ ∘ first r)
  -- --   ≈⟨ ∘≈ {_⇨′_ = _⇨ₘ_} (firstₖ f ⟦∘⟧ ⌞ assocˡ ⌟)
  -- --         (∘≈ʳ {_⇨′_ = _⇨ₘ_} (F-∘ assocʳ (first r))) ⟩
  -- --     (⟦ firstₖ f ⟧ₖ ∘ ⟦ assocˡ ⟧ᵣ) ∘ first (Fₘ p) ∘ (⟦ assocʳ ⟧ᵣ ∘ ⟦ first r ⟧ᵣ)
  -- --   ≈˘⟨ ∘≈ʳ {_⇨′_ = _⇨ₘ_} (assoc {_⇨′_ = _⇨ₘ_}) ⟩
  -- --     (⟦ firstₖ f ⟧ₖ ∘ ⟦ assocˡ ⟧ᵣ) ∘ (first (Fₘ p) ∘ ⟦ assocʳ ⟧ᵣ) ∘ ⟦ first r ⟧ᵣ
  -- --   ≈⟨ assoc {_⇨′_ = _⇨ₘ_} ⟩
  -- --     ⟦ firstₖ f ⟧ₖ ∘ ⟦ assocˡ ⟧ᵣ ∘ (first (Fₘ p) ∘ ⟦ assocʳ ⟧ᵣ) ∘ ⟦ first r ⟧ᵣ
  -- --   ≈˘⟨ ∘≈ʳ {_⇨′_ = _⇨ₘ_} (assoc {_⇨′_ = _⇨ₘ_}) ⟩
  -- --     ⟦ firstₖ f ⟧ₖ ∘ (⟦ assocˡ ⟧ᵣ ∘ first (Fₘ p) ∘ ⟦ assocʳ ⟧ᵣ) ∘ ⟦ first r ⟧ᵣ
  -- --   ≈⟨ ∘≈ʳ {_⇨′_ = _⇨ₘ_} (∘≈ {_⇨′_ = _⇨ₘ_} (∘≈ {_⇨′_ = _⇨ₘ_} F-assocˡ (∘≈ʳ {_⇨′_ = _⇨ₘ_} F-assocʳ)) (F-first r)) ⟩
  -- --     ⟦ firstₖ f ⟧ₖ ∘ (assocᴴˡ ∘ first (Fₘ p) ∘ assocᴴʳ) ∘ firstᴴ ⟦ r ⟧ᵣ
  -- --   ≈⟨ ∘≈ʳ (∘≈ˡ {!!}) ⟩
  -- --     firstᴴ ⟦ f ⟧ₖ ∘ firstᴴ (first (Fₘ p)) ∘ firstᴴ ⟦ r ⟧ᵣ
  -- --   ≈⟨ ∘≈ʳ {_⇨′_ = _⇨ₘ_} first∘firstᴴ ⟩
  -- --     firstᴴ ⟦ f ⟧ₖ ∘ firstᴴ (first (Fₘ p) ∘ ⟦ r ⟧ᵣ)
  -- --   ≈⟨ first∘firstᴴ ⟩
  -- --     firstᴴ (⟦ f ⟧ₖ ∘ first (Fₘ p) ∘ ⟦ r ⟧ᵣ)
  -- --   ≡⟨⟩
  -- --     first ⟦ f ∘·first p ∘ r ⟧ₖ
  -- --   ∎

  -- ⟦second⟧ : (g : b ⇨ d) → ⟦ secondₖ {a = a} g ⟧ₖ ≈ secondᴴ ⟦ g ⟧ₖ
  -- ⟦second⟧ g = {!!}

  -- infixr 7 _⟦⊗⟧_
  -- _⟦⊗⟧_ : ∀ (f : a ⇨ c) (g : b ⇨ d) → ⟦ f ⊗ g ⟧ₖ ≈ ⟦ f ⟧ₖ ⊗ᴴ ⟦ g ⟧ₖ

  -- f ⟦⊗⟧ g =
  --   begin
  --     ⟦ f ⊗ g ⟧ₖ
  --   ≡⟨⟩
  --     ⟦ secondₖ g ∘ firstₖ f ⟧ₖ
  --   ≈⟨ secondₖ g ⟦∘⟧ firstₖ f ⟩
  --     ⟦ secondₖ g ⟧ₖ ∘ ⟦ firstₖ f ⟧ₖ
  --     ≈⟨ ∘≈ {_⇨′_ = _⇨ₘ_} (⟦second⟧ g) (⟦first⟧ f) ⟩
  --     secondᴴ ⟦ g ⟧ₖ ∘ firstᴴ ⟦ f ⟧ₖ
  --   ≈⟨ second∘firstᴴ ⟩
  --     ⟦ f ⟧ₖ ⊗ᴴ ⟦ g ⟧ₖ
  --   ∎


module linearize-homomorphism-instances where

  instance

    categoryH : CategoryH _⇨_ _⇨ₘ_
    categoryH = record
     { F-id = F-id {_⇨₁_ = _⇨ᵣ_}
     ; F-∘  = λ { {g = g}{f} → g ⟦∘⟧ f }
     }

    -- Also CartesianH and LogicH

    cartesianH : CartesianH _⇨_ _⇨ₘ_
    cartesianH = record
      { F-! = {!!}
      ; F-▵ = {!!}
      ; F-exl = {!!}
      ; F-exr = {!!}
      }

{-

-}
