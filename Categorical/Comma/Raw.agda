{-# OPTIONS --safe --without-K #-}

open import Level

open import Categorical.Raw
open import Categorical.Equiv
open import Categorical.Laws as L hiding (Category; Cartesian)
open import Categorical.Homomorphism

module Categorical.Comma.Raw
   {o₁}{obj₁ : Set o₁} ⦃ _ : Products obj₁ ⦄
     {ℓ₁} (_⇨₁_ : obj₁ → obj₁ → Set ℓ₁) ⦃ _ : Cartesian _⇨₁_ ⦄
   {o₂}{obj₂ : Set o₂} ⦃ _ : Products obj₂ ⦄
     {ℓ₂} (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂) ⦃ _ : Cartesian _⇨₂_ ⦄
   {o₃}{obj₃ : Set o₃} ⦃ _ : Products obj₃ ⦄
     {ℓ₃} (_⇨₃_ : obj₃ → obj₃ → Set ℓ₃) ⦃ _ : Cartesian _⇨₃_ ⦄
   {q} ⦃ _ : Equivalent q _⇨₃_ ⦄ ⦃ _ : L.Cartesian _⇨₃_ ⦄
   ⦃ _ : Homomorphismₒ obj₁ obj₃ ⦄ ⦃ _ : Homomorphism _⇨₁_ _⇨₃_ ⦄
     ⦃ _ : CategoryH _⇨₁_ _⇨₃_ ⦄ ⦃ _ : ProductsH obj₁ _⇨₃_ ⦄
     ⦃ _ : CartesianH _⇨₁_ _⇨₃_ ⦄
   ⦃ _ : Homomorphismₒ obj₂ obj₃ ⦄ ⦃ _ : Homomorphism _⇨₂_ _⇨₃_ ⦄
     ⦃ _ : CategoryH _⇨₂_ _⇨₃_ ⦄ ⦃ _ : ProductsH obj₂ _⇨₃_ ⦄
     ⦃ _ : CartesianH _⇨₂_ _⇨₃_ ⦄
 where

open import Categorical.Comma.Type _⇨₁_ _⇨₂_ _⇨₃_ public

module comma-raw-instances where

  instance
    open Obj
    open ≈-Reasoning
  
    category : Category _⇨_
    category = record
      { id  = λ {a} → mk id id
          (begin
             h a ∘ Fₘ id
           ≈⟨ ∘≈ʳ F-id ⟩
             h a ∘ id
           ≈⟨ identityʳ ⟩
             h a
           ≈˘⟨ identityˡ ⟩
             id ∘ h a
           ≈˘⟨ ∘≈ˡ F-id ⟩
             Fₘ id ∘ h a
           ∎)
      ; _∘_ = λ {a b c} (mk g₁ g₂ comm-g) (mk f₁ f₂ comm-f) →
          mk (g₁ ∘ f₁) (g₂ ∘ f₂)
           (begin
              h c ∘ Fₘ (g₁ ∘ f₁)
            ≈⟨ ∘≈ʳ F-∘ ⟩
              h c ∘ (Fₘ g₁ ∘ Fₘ f₁)
            ≈˘⟨ assoc ⟩
              (h c ∘ Fₘ g₁) ∘ Fₘ f₁
            ≈⟨ ∘≈ˡ comm-g ⟩
              (Fₘ g₂ ∘ h b) ∘ Fₘ f₁
            ≈⟨ assoc ⟩
              Fₘ g₂ ∘ (h b ∘ Fₘ f₁)
            ≈⟨ ∘≈ʳ comm-f ⟩
              Fₘ g₂ ∘ (Fₘ f₂ ∘ h a)
            ≈˘⟨ assoc ⟩
              (Fₘ g₂ ∘ Fₘ f₂) ∘ h a
            ≈˘⟨ ∘≈ˡ F-∘ ⟩
              Fₘ (g₂ ∘ f₂) ∘ h a
            ∎)
      }

    products : Products Obj
    products = record { ⊤   = mk (ε ∘ ε⁻¹)
                      ; _×_ = λ (mk h) (mk k) → mk (μ ∘ (h ⊗ k) ∘ μ⁻¹)
                      }

    cartesian : Cartesian _⇨_
    cartesian = record
      { ! = λ {a} → mk ! !
         (begin
            h ⊤ ∘ Fₘ !
          ≡⟨⟩
            (ε ∘ ε⁻¹) ∘ Fₘ !
          ≈⟨ ∘≈ʳ F-! ⟩
            (ε ∘ ε⁻¹) ∘ (ε ∘ !)
          ≈⟨ cancelInner ε⁻¹∘ε ⟩
            ε ∘ !
          ≈˘⟨ ∘≈ʳ ∀⊤ ⟩  -- Universal property for !
            ε ∘ (! ∘ h a)
          ≈˘⟨ assoc ⟩
            (ε ∘ !) ∘ h a
          ≈˘⟨ ∘≈ˡ F-! ⟩
            Fₘ ! ∘ h a
          ∎)
      ; exl = λ {a b} → mk exl exl
          (begin
             h a ∘ Fₘ exl
           ≈˘⟨ ∘≈ʳ (identityʳ • ∘≈ʳ μ∘μ⁻¹) ⟩
             h a ∘ (Fₘ exl ∘ μ ∘ μ⁻¹)
           ≈⟨ ∘≈ʳ (∘≈ˡ F-exl • sym assoc) ⟩
              h a ∘ (exl ∘ μ⁻¹)
           ≈˘⟨ assoc ⟩
              (h a ∘ exl) ∘ μ⁻¹
           ≈˘⟨ ∘≈ˡ exl∘▵ ⟩
              (exl ∘ (h a ⊗ h b)) ∘ μ⁻¹
           ≈⟨ assoc ⟩
              exl ∘ (h a ⊗ h b) ∘ μ⁻¹
           ≈˘⟨ ∘≈ˡ F-exl ⟩
             (Fₘ exl ∘ μ) ∘ (h a ⊗ h b) ∘ μ⁻¹
           ≈⟨ ∘≈ʳ (sym assoc) • assoc ⟩
             Fₘ exl ∘ (μ ∘ (h a ⊗ h b)) ∘ μ⁻¹
           ≈⟨ ∘≈ʳ assoc ⟩
             Fₘ exl ∘ μ ∘ (h a ⊗ h b) ∘ μ⁻¹
           ≡⟨⟩
             Fₘ exl ∘ h (a × b)
           ∎)
      ; exr = λ {a b} → mk exr exr
          (begin
             h b ∘ Fₘ exr
           ≈˘⟨ ∘≈ʳ (identityʳ • ∘≈ʳ μ∘μ⁻¹) ⟩
             h b ∘ (Fₘ exr ∘ μ ∘ μ⁻¹)
           ≈⟨ ∘≈ʳ (∘≈ˡ F-exr • sym assoc) ⟩
              h b ∘ (exr ∘ μ⁻¹)
           ≈˘⟨ assoc ⟩
              (h b ∘ exr) ∘ μ⁻¹
           ≈˘⟨ ∘≈ˡ exr∘▵ ⟩
              (exr ∘ (h a ⊗ h b)) ∘ μ⁻¹
           ≈⟨ assoc ⟩
              exr ∘ (h a ⊗ h b) ∘ μ⁻¹
           ≈˘⟨ ∘≈ˡ F-exr ⟩
             (Fₘ exr ∘ μ) ∘ (h a ⊗ h b) ∘ μ⁻¹
           ≈⟨ ∘≈ʳ (sym assoc) • assoc ⟩
             Fₘ exr ∘ (μ ∘ (h a ⊗ h b)) ∘ μ⁻¹
           ≈⟨ ∘≈ʳ assoc ⟩
             Fₘ exr ∘ μ ∘ (h a ⊗ h b) ∘ μ⁻¹
           ≡⟨⟩
             Fₘ exr ∘ h (a × b)
           ∎)
      ; _▵_ = λ {a c d} (mk f₁ f₂ comm-f) (mk g₁ g₂ comm-g) →
          mk (f₁ ▵ g₁) (f₂ ▵ g₂)
            (begin
               h (c × d) ∘ Fₘ (f₁ ▵ g₁)
             ≈⟨ ∘≈ʳ F-▵ ⟩
               (μ ∘ (h c ⊗ h d) ∘ μ⁻¹) ∘ (μ ∘ (Fₘ f₁ ▵ Fₘ g₁))
             ≈˘⟨ ∘≈ˡ assoc ⟩
               ((μ ∘ (h c ⊗ h d)) ∘ μ⁻¹) ∘ (μ ∘ (Fₘ f₁ ▵ Fₘ g₁))
             ≈⟨ cancelInner μ⁻¹∘μ ⟩
               (μ ∘ (h c ⊗ h d)) ∘ (Fₘ f₁ ▵ Fₘ g₁)
             ≈⟨ assoc ⟩
               μ ∘ (h c ⊗ h d) ∘ (Fₘ f₁ ▵ Fₘ g₁)
             ≈⟨ ∘≈ʳ ⊗∘▵ ⟩
               μ ∘ (h c ∘ Fₘ f₁ ▵ h d ∘ Fₘ g₁)
             ≈⟨ ∘≈ʳ (▵≈ comm-f comm-g) ⟩
               μ ∘ (Fₘ f₂ ∘ h a ▵ Fₘ g₂ ∘ h a)
             ≈˘⟨ ∘≈ʳ ▵∘ ⟩
               μ ∘ ((Fₘ f₂ ▵ Fₘ g₂) ∘ h a)
             ≈˘⟨ assoc ⟩
               (μ ∘ (Fₘ f₂ ▵ Fₘ g₂)) ∘ h a
             ≈˘⟨ ∘≈ˡ F-▵ ⟩
               Fₘ (f₂ ▵ g₂) ∘ h a
             ∎)
      }

    -- TODO: CartesianClosed and Logic.
