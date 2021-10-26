-- *Full* subcategory or something like it. Note that the I → obj homomorphism
-- needn't be injective.
{-# OPTIONS --safe --without-K #-}

open import Level

open import Categorical.Homomorphism
open import Categorical.Laws as L hiding (Category; Cartesian)
open import Categorical.Reasoning

module Categorical.Subcategory
  {o ℓ} {obj : Set o} (_↠_ : obj → obj → Set ℓ)
  {i} (I : Set i) ⦃ _ : Homomorphismₒ I obj ⦄
  ⦃ _ : Category _↠_ ⦄ {q : Level} ⦃ _ : Equivalent q _↠_ ⦄
 where

infix 4 _⇨_
record _⇨_ (a b : I) : Set ℓ where
  constructor mk
  field
    f : Fₒ a ↠ Fₒ b

module subcategory-instances where

  refl↠ : ∀ {a b}{f : a ↠ b} → f ≈ f
  refl↠ = refl

  instance
    category : Category _⇨_
    category = record { id = mk id ; _∘_ = λ (mk g) (mk f) → mk (g ∘ f) }

    cartesian : ⦃ _ : Products obj ⦄ ⦃ _ : Cartesian _↠_ ⦄
                ⦃ _ : Products I ⦄ ⦃ _ : ProductsH I _↠_ ⦄ →
                Cartesian _⇨_
    cartesian = record { !   = mk (ε ∘ !)
                       ; _▵_ = λ (mk f) (mk g) → mk (μ ∘ (f ▵ g))
                       ; exl = mk (exl ∘ μ⁻¹)
                       ; exr = mk (exr ∘ μ⁻¹)
                       }

    H : Homomorphism _⇨_ _↠_
    H = record { Fₘ = λ (mk f) → f }

    equivalent : Equivalent q _⇨_
    equivalent = H-equiv

    categoryH : CategoryH _⇨_ _↠_
    categoryH = record { F-id = refl↠ ; F-∘ = refl↠ }

    cartesianH :
      ⦃ _ : Products obj ⦄ ⦃ _ : Cartesian _↠_ ⦄ ⦃ _ : L.Category _↠_ ⦄
      ⦃ _ : Products I ⦄ ⦃ _ : ProductsH I _↠_ ⦄ →
      CartesianH _⇨_ _↠_
    cartesianH = record { F-! = refl↠
                        ; F-▵ = refl↠
                        ; F-exl = ∘-assoc-elimʳ μ⁻¹∘μ   -- (exl ∘ μ⁻¹) ∘ μ ≈ exl
                        ; F-exr = ∘-assoc-elimʳ μ⁻¹∘μ   -- (exr ∘ μ⁻¹) ∘ μ ≈ exr
                        }

    open import Categorical.MakeLawful _⇨_ _↠_

    l-category : ⦃ _ : L.Category _↠_ ⦄ → L.Category _⇨_
    l-category = LawfulCategoryᶠ
