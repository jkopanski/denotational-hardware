-- Arrow categories. Specializes comma categories with identity functors.
{-# OPTIONS --safe --without-K #-}

open import Level

open import Categorical.Raw
open import Categorical.Equiv
open import Categorical.Laws as L hiding (Category; Cartesian)
open import Categorical.Homomorphism

module Categorical.Arrow
   {o}{obj : Set o} ⦃ _ : Products obj ⦄
   {ℓ} (_↠_ : obj → obj → Set ℓ) ⦃ _ : Category _↠_ ⦄ ⦃ _ : Cartesian _↠_ ⦄
   {q} ⦃ _ : Equivalent q _↠_ ⦄ ⦃ _ : L.Category _↠_ ⦄ ⦃ _ : L.Cartesian _↠_ ⦄
 where

private
  instance

    Hₒ : Homomorphismₒ obj obj
    Hₒ = id-Hₒ

    H : Homomorphism _↠_ _↠_
    H = id-H

    catH : CategoryH _↠_ _↠_
    catH = id-CategoryH

    prodH : ProductsH obj _↠_
    prodH = id-ProductsH

    cartH : CartesianH _↠_ _↠_
    cartH = id-CartesianH

    -- TODO: Replace Hₒ, H, etc by a bundle

-- open import Categorical.Comma.Type _↠_ _↠_ _↠_ ⦃ ch₁ = catH ⦄ ⦃ ch₂ = catH ⦄ public

open import Categorical.Comma.Raw _↠_ _↠_ _↠_
  ⦃ catH₁ = catH ⦄ ⦃ cartH₁ = cartH ⦄
  ⦃ catH₂ = catH ⦄ ⦃ cartH₂ = cartH ⦄
  public

-- Transposition
_ᵀ : ∀ {a b} ((mk f₁ f₂ _) : a ⇨ b) → (f₁ ⇉ f₂)
_ᵀ {mk h}{mk h′} (mk _ _ commute) = mk h h′ (sym commute)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Vertical composition.
infixr 9 _◎_
_◎_ : ∀ {τ₁ τ₂ τ₃ : obj} {τ₁′ τ₂′ τ₃′ : obj}
        {h : τ₁ ↠ τ₂} {h′ : τ₁′ ↠ τ₂′}
        {k : τ₂ ↠ τ₃} {k′ : τ₂′ ↠ τ₃′}
        ((mk fₖ₁ _ _) : k ⇉ k′) ((mk _ fₕ₂ _) : h ⇉ h′) → ⦃ fₖ₁ ≡ fₕ₂ ⦄
    → k ∘ h ⇉ k′ ∘ h′
(G ◎ F) ⦃ refl ⦄ = (G ᵀ ∘ F ᵀ) ᵀ
