{-# OPTIONS --safe --without-K #-}

module Categorical.Laws where

open import Level

open import Categorical.Raw as R hiding (Category; Cartesian)
open import Categorical.Equiv

open ≈-Reasoning

private
  variable
    o ℓ o₁ ℓ₁ o₂ ℓ₂ : Level
    obj obj₁ obj₂ : Set o
    a b c d e : obj
    a′ b′ c′ d′ e′ : obj

record Category {obj : Set o} (_⇨′_ : obj → obj → Set ℓ)
                q ⦃ equiv : Equivalent q _⇨′_ ⦄
                ⦃ ⇨Category : R.Category _⇨′_ ⦄
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

open Category ⦃ … ⦄ public


record Cartesian {obj : Set o} ⦃ _ : Products obj ⦄ (_⇨′_ : obj → obj → Set ℓ)
                 q ⦃ equiv : Equivalent q _⇨′_ ⦄
                 ⦃ _ : R.Cartesian _⇨′_ ⦄
       : Set (suc o ⊔ ℓ ⊔ suc q) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    ⦃ ⇨Category ⦄ : Category _⇨_ q
    exl▵exr : ∀ {a b : obj} → exl ▵ exr ≈ id {a = a × b}
    -- ...

    ▵≈ : ∀ {f g : a ⇨ c} {h k : a ⇨ d} → h ≈ k → f ≈ g → h ▵ f ≈ k ▵ g

  ▵≈ˡ : ∀ {f : a ⇨ c} {h k : a ⇨ d} → h ≈ k → h ▵ f ≈ k ▵ f
  ▵≈ˡ h≈k = ▵≈ h≈k refl

  ▵≈ʳ : ∀ {f g : a ⇨ c} {h : a ⇨ d} → f ≈ g → h ▵ f ≈ h ▵ g
  ▵≈ʳ f≈g = ▵≈ refl f≈g

  id⊗id : ∀ {a b : obj} → id ⊗ id ≈ id {a = a × b}
  id⊗id = exl▵exr • ▵≈ identityˡ identityˡ

open Cartesian ⦃ … ⦄ public

-- TODO: CartesianClosed, Logic etc.

-- TODO: Convert homomorphisms into lawfuls.
