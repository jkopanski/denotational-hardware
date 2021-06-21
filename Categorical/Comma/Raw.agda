{-# OPTIONS --safe --without-K #-}

open import Level

open import Categorical.Raw
open import Categorical.Equiv
open import Categorical.Laws as L hiding (Category; Cartesian)
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

{-

    -- TODO: Cartesian, CartesianClosed, and Logic.

    products : ⦃ p₁ : Products obj₁ ⦄ ⦃ p₂ : Products obj₂ ⦄ ⦃ p₃ : Products obj₃ ⦄
               ⦃ c₃ : Cartesian _⇨₃_ ⦄
               ⦃ ph₁ : ProductsH obj₁ _⇨₃_ ⦄ ⦃ ph₂ : ProductsH obj₂ _⇨₃_ ⦄ 
             → Products Obj

    products ⦃ p₁ = p₁ ⦄ ⦃ p₂ = p₂ ⦄ ⦃ p₃ = p₃ ⦄
             = record { ⊤ = mk {mp₁.⊤}{mp₂.⊤} {!!}
                                      -- ({!!} ∘ {!!})
                                      -- (ε {obj₁ = obj₂}{_⇨₂′_ = _⇨₃_} ∘ ε⁻¹ {obj₁ = obj₁}{_⇨₂′_ = _⇨₃_})
                            -- mk {⊤}{⊤} (ε ∘ Products.ε⁻¹ p₁)
                                      -- (ε ∘ ε⁻¹)

                      -- ; _×_ = λ (mk h) (mk k) → mk (μ ∘ (h ⊗ k) ∘ μ⁻¹)

                      -- ; _×_ = λ (mk {σ₁}{σ₂} h) (mk {τ₁}{τ₂} k) →
                      --              mk {σ₁ × τ₁} {σ₂ × τ₂} (μ ∘ (h ⊗ k) ∘ μ⁻¹)

                      ; _×_ = λ (mk {σ₁}{σ₂} h) (mk {τ₁}{τ₂} k) →
                                   {!!}

                      }
      where module mp₁ = Products p₁
            module mp₂ = Products p₂
            module mp₃ = Products p₃

            ε⁻¹* : Fₒ mp₁.⊤ ⇨₃ mp₃.⊤
            ε⁻¹* = ε⁻¹
            ε* : mp₃.⊤ ⇨₃ Fₒ mp₂.⊤
            ε* = ε
            ⊤* : Fₒ mp₁.⊤ ⇨₃ Fₒ mp₂.⊤
            ⊤* = ε* ∘ ε⁻¹*

-- The problem is that I'm getting one cat3 with the module and another in the
-- cart3. I can take a Cartesian in the module instead, but next we'll have to
-- require CartesianClosed, which precludes some categories. I could remove
-- change the Category *field* in Cartesian to an instance parameter and
-- likewise for CartesianClosed, further bloating signatures. Is there another
-- solution? I think I need some Agda advice. If I do replace more fields with
-- parameters, also add bundles, so at least clients are uncluttered.

-}

-- record Obj : Set (o₁ ⊔ o₂ ⊔ ℓ₃) where
--   constructor mk
--   field
--     { τ₁ } : obj₁
--     { τ₂ } : obj₂
--     h : Fₒ τ₁ ⇨₃ Fₒ τ₂

-- goal Fₒ ⊤₁ ⇨₃ Fₒ ⊤₂

-- ε⁻¹ : Fₒ ⊤ ⇨₃ ⊤
-- ε : ⊤ ⇨₃ Fₒ ⊤

-- μ⁻¹ : Fₒ (σ₁ × τ₁) ⇨₃ Fₒ σ₁ × Fₒ τ₁
-- h ⊗ k : Fₒ σ₁ × Fₒ τ₁ ⇨ Fₒ σ₂ × Fₒ τ₂
-- μ : Fₒ σ₂ × Fₒ τ₂ ⇨₃ Fₒ (σ₂ × τ₂)



-- Fₒ (σ₁ × τ₁) ⇨₃ Fₒ (σ₂ × τ₂)


    -- cartesian : CartesianClosed _⇨_
    -- cartesian = ?
