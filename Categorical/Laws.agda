{-# OPTIONS --safe --without-K #-}

module Categorical.Laws where

open import Level

open import Categorical.Raw
open import Categorical.Equiv

open ≈-Reasoning

private
  variable
    o ℓ o₁ ℓ₁ o₂ ℓ₂ : Level
    obj obj₁ obj₂ : Set o
    a b c d e : obj
    a′ b′ c′ d′ e′ : obj

record LawfulCategory {obj : Set o} (_⇨′_ : obj → obj → Set ℓ)
                      q ⦃ equiv : Equivalent q _⇨′_ ⦄
                      ⦃ ⇨Category : Category _⇨′_ ⦄
       : Set (suc o ⊔ ℓ ⊔ suc q) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    identityˡ : {f : a ⇨ b} → id ∘ f ≈ f
    identityʳ : {f : a ⇨ b} → f ∘ id ≈ f
    assoc     : {f : a ⇨ b} {g : b ⇨ c} {h : c ⇨ d}
              → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)

    ∘≈ : ∀ {f g : a ⇨ b} {h k : b ⇨ c} → h ≈ k → f ≈ g → h ∘ f ≈ k ∘ g

  ∘≈ˡ : ∀ {f : a ⇨ b} {h k : b ⇨ c} → h ≈ k → h ∘ f ≈ k ∘ f
  ∘≈ˡ h≈k = ∘≈ h≈k refl

  ∘≈ʳ : ∀ {f g : a ⇨ b} {h : b ⇨ c} → f ≈ g → h ∘ f ≈ h ∘ g
  ∘≈ʳ f≈g = ∘≈ refl f≈g

-- TODO: LawfulCartesian etc.

-- TODO: Convert homomorphisms into lawfuls.

