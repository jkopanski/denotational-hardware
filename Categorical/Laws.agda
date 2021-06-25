{-# OPTIONS --safe --without-K #-}

module Categorical.Laws where

open import Level

open import Categorical.Raw as R hiding (Category; Cartesian; CartesianClosed)
open import Categorical.Equiv
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function.Equivalence using (_⇔_; module Equivalence)
open import Function.Equality using (_⟨$⟩_)

open Equivalence
open ≈-Reasoning

private
  variable
    o ℓ : Level
    obj : Set o
    a b c d : obj

record Category {obj : Set o} (_⇨′_ : obj → obj → Set ℓ)
                q ⦃ equiv : Equivalent q _⇨′_ ⦄
                ⦃ _ : R.Category _⇨′_ ⦄
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

open import Data.Product using (_,_) renaming (_×_ to _×ₚ_)

record Cartesian {obj : Set o} ⦃ _ : Products obj ⦄
                 (_⇨′_ : obj → obj → Set ℓ)
                 q ⦃ _ : Equivalent q _⇨′_ ⦄
                 ⦃ _ : R.Cartesian _⇨′_ ⦄
       : Set (suc o ⊔ ℓ ⊔ suc q) where
  private infix 0 _⇨_; _⇨_ = _⇨′_

  field
    ⦃ ⇨Category ⦄ : Category _⇨_ q

    ∀× : ∀ {f : a ⇨ b} {g : a ⇨ c} {k : a ⇨ b × c}
       → (k ≈ f ▵ g) ⇔ (exl ∘ k ≈ f  ×ₚ  exr ∘ k ≈ g)

    ▵≈ : ∀ {f g : a ⇨ c} {h k : a ⇨ d} → h ≈ k → f ≈ g → h ▵ f ≈ k ▵ g

  ▵≈ˡ : ∀ {f : a ⇨ c} {h k : a ⇨ d} → h ≈ k → h ▵ f ≈ k ▵ f
  ▵≈ˡ h≈k = ▵≈ h≈k refl

  ▵≈ʳ : ∀ {f g : a ⇨ c} {h : a ⇨ d} → f ≈ g → h ▵ f ≈ h ▵ g
  ▵≈ʳ f≈g = ▵≈ refl f≈g

  exl▵exr : ∀ {a b : obj} → exl ▵ exr ≈ id {a = a × b}
  exl▵exr = sym (from ∀× ⟨$⟩ (identityʳ , identityʳ))

  id⊗id : ∀ {a b : obj} → id ⊗ id ≈ id {a = a × b}
  id⊗id = exl▵exr • ▵≈ identityˡ identityˡ


open Cartesian ⦃ … ⦄ public

record CartesianClosed {obj : Set o} ⦃ _ : Products obj ⦄
                       ⦃ _ : Exponentials obj ⦄ (_⇨′_ : obj → obj → Set ℓ)
                       q ⦃ _ : Equivalent q _⇨′_ ⦄
                       ⦃ _ : Products (Set q) ⦄
                       ⦃ _ : R.CartesianClosed _⇨′_ ⦄
       : Set (suc o ⊔ ℓ ⊔ suc q) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    ⦃ ⇨Cartesian ⦄ : Cartesian _⇨_ q

    ∀⇛ : ∀ {f : a × b ⇨ c} {g : a ⇨ (b ⇛ c)} → (g ≈ curry f) ⇔ (f ≈ uncurry g)
    -- Note: uncurry g ≡ apply ∘ first g ≡ apply ∘ (g ⊗ id)
    -- RHS is often written "apply ∘ (g ⊗ id)"

    curry≈ : ∀ {f g : a × b ⇨ c} → f ≈ g → curry f ≈ curry g

  curry-apply : ∀ {a b : obj} → id { a = a ⇛ b } ≈ curry apply
  curry-apply = from ∀⇛ ⟨$⟩
                  (begin
                     apply
                   ≈˘⟨ identityʳ ⟩
                     apply ∘ id
                   ≈˘⟨ ∘≈ʳ id⊗id ⟩
                     apply ∘ (id ⊗ id)
                   ≡⟨⟩
                     apply ∘ first id
                   ≡⟨⟩
                     uncurry id
                   ∎)

-- TODO: Logic
