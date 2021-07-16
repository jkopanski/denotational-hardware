{-# OPTIONS --safe --without-K #-}

module Categorical.Laws where

open import Level
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function.Equivalence using (_⇔_; module Equivalence)
open import Function.Equality using (_⟨$⟩_)

open import Categorical.Raw as R hiding (Category; Cartesian; CartesianClosed)
open import Categorical.Equiv
open import Functions.Raw

open Equivalence
open ≈-Reasoning

private
  variable
    o ℓ : Level
    obj : Set o
    a b c d e : obj

record Category {obj : Set o} (_⇨′_ : obj → obj → Set ℓ)
                {q} ⦃ equiv : Equivalent q _⇨′_ ⦄
                ⦃ rcat : R.Category _⇨′_ ⦄
       : Set (suc o ⊔ ℓ ⊔ suc q) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    identityˡ : {f : a ⇨ b} → id ∘ f ≈ f
    identityʳ : {f : a ⇨ b} → f ∘ id ≈ f
    assoc     : {f : a ⇨ b} {g : b ⇨ c} {h : c ⇨ d} → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)

    -- TODO: infix?
    ∘≈ : ∀ {f g : a ⇨ b} {h k : b ⇨ c} → h ≈ k → f ≈ g → h ∘ f ≈ k ∘ g

  -- TODO: replace the assoc field after I've inspected all uses
  ∘-assocʳ : {f : a ⇨ b} {g : b ⇨ c} {h : c ⇨ d} → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
  ∘-assocʳ = assoc

  ∘-assocˡ : {f : a ⇨ b} {g : b ⇨ c} {h : c ⇨ d} → h ∘ (g ∘ f) ≈ (h ∘ g) ∘ f
  ∘-assocˡ = sym ∘-assocʳ

  ∘≈ˡ : ∀ {f : a ⇨ b} {h k : b ⇨ c} → h ≈ k → h ∘ f ≈ k ∘ f
  ∘≈ˡ h≈k = ∘≈ h≈k refl

  ∘≈ʳ : ∀ {f g : a ⇨ b} {h : b ⇨ c} → f ≈ g → h ∘ f ≈ h ∘ g
  ∘≈ʳ f≈g = ∘≈ refl f≈g

  -- Taken from Categories.Morphism.Reasoning.Core in agda-categories.
  -- I'll probably add more and move them to another module.

  center : ∀ {f : a ⇨ b}{g : b ⇨ c}{h : c ⇨ d}{i : d ⇨ e}{hg : b ⇨ d}
         → h ∘ g ≈ hg → (i ∘ h) ∘ (g ∘ f) ≈ i ∘ hg ∘ f
  center {f = f}{g}{h}{i}{hg} h∘g≈hg =
    begin
      (i ∘ h) ∘ (g ∘ f)
    ≈⟨ assoc ⟩
      i ∘ h ∘ (g ∘ f)
    ≈˘⟨ ∘≈ʳ assoc ⟩
      i ∘ (h ∘ g) ∘ f
    ≈⟨ ∘≈ʳ (∘≈ˡ h∘g≈hg) ⟩
      i ∘ hg ∘ f
    ∎

  cancelInner : ∀ {f : a ⇨ b}{g : b ⇨ c}{h : c ⇨ b}{i : b ⇨ d}
              → h ∘ g ≈ id → (i ∘ h) ∘ (g ∘ f) ≈ i ∘ f
  cancelInner {f = f}{g}{h}{i} h∘g≈id =
    begin
      (i ∘ h) ∘ (g ∘ f)
    ≈⟨ center h∘g≈id ⟩
      i ∘ id ∘ f
    ≈⟨ ∘≈ʳ identityˡ ⟩
      i ∘ f
    ∎

open Category ⦃ … ⦄ public

open import Data.Product using (_,_) renaming (_×_ to _×ₚ_)

record Cartesian {obj : Set o} ⦃ _ : Products obj ⦄
                 (_⇨′_ : obj → obj → Set ℓ)
                 {q} ⦃ _ : Equivalent q _⇨′_ ⦄
                 ⦃ _ : R.Category _⇨′_ ⦄ ⦃ _ : R.Cartesian _⇨′_ ⦄
                 ⦃ ⇨Category : Category _⇨′_ ⦄
       : Set (suc o ⊔ ℓ ⊔ suc q) where
  private infix 0 _⇨_; _⇨_ = _⇨′_

  field
    ∀⊤ : ∀ {f : a ⇨ ⊤} → f ≈ !

    ∀× : ∀ {f : a ⇨ b} {g : a ⇨ c} {k : a ⇨ b × c}
       → k ≈ f ▵ g ⇔ (exl ∘ k ≈ f  ×ₚ  exr ∘ k ≈ g)

    -- TODO: infix?
    ▵≈ : ∀ {f g : a ⇨ c} {h k : a ⇨ d} → h ≈ k → f ≈ g → h ▵ f ≈ k ▵ g

  ∀×→ : ∀ {f : a ⇨ b} {g : a ⇨ c} {k : a ⇨ b × c}
     → k ≈ f ▵ g → (exl ∘ k ≈ f  ×ₚ  exr ∘ k ≈ g)
  ∀×→ = to ∀× ⟨$⟩_

  ∀×← : ∀ {f : a ⇨ b} {g : a ⇨ c} {k : a ⇨ b × c}
     → (exl ∘ k ≈ f  ×ₚ  exr ∘ k ≈ g) → k ≈ f ▵ g
  ∀×← = from ∀× ⟨$⟩_

  ▵≈ˡ : ∀ {f : a ⇨ c} {h k : a ⇨ d} → h ≈ k → h ▵ f ≈ k ▵ f
  ▵≈ˡ h≈k = ▵≈ h≈k refl

  ▵≈ʳ : ∀ {f g : a ⇨ c} {h : a ⇨ d} → f ≈ g → h ▵ f ≈ h ▵ g
  ▵≈ʳ f≈g = ▵≈ refl f≈g

  open import Data.Product using (proj₁; proj₂)
  -- TODO: Generalize Function category from level 0, and use exl & exr in place
  -- of proj₁ & proj₂

  exl∘▵ : ∀ {f : a ⇨ b}{g : a ⇨ c} → exl ∘ (f ▵ g) ≈ f
  exl∘▵ = proj₁ (∀×→ refl)

  exr∘▵ : ∀ {f : a ⇨ b}{g : a ⇨ c} → exr ∘ (f ▵ g) ≈ g
  exr∘▵ = proj₂ (∀×→ refl)

  -- Specializing:
  -- exl∘▵ : ∀ {f : a ⇨ c}{g : b ⇨ d} → exl ∘ (f ⊗ g) ≈ f ∘ exl
  -- exr∘▵ : ∀ {f : a ⇨ c}{g : b ⇨ d} → exr ∘ (f ⊗ g) ≈ g ∘ exr

  exl∘▵exr : ∀ {a b : obj} → exl ▵ exr ≈ id {a = a × b}
  exl∘▵exr = sym (∀×← (identityʳ , identityʳ))

  id⊗id : ∀ {a b : obj} → id ⊗ id ≈ id {a = a × b}
  id⊗id = exl∘▵exr • ▵≈ identityˡ identityˡ

  ▵∘ : ∀ {f : a ⇨ b}{g : b ⇨ c}{h : b ⇨ d} → (g ▵ h) ∘ f ≈ g ∘ f ▵ h ∘ f
  ▵∘ {f = f}{g}{h}= ∀×← (∘≈ˡ exl∘▵ • sym assoc , ∘≈ˡ exr∘▵ • sym assoc)
  -- exl ∘ ((g ▵ h) ∘ f) ≈ g ∘ f

  ⊗∘▵ : ∀ {f : a ⇨ b}{g : a ⇨ c}{h : b ⇨ d}{k : c ⇨ e}
      → (h ⊗ k) ∘ (f ▵ g) ≈ h ∘ f ▵ k ∘ g
  ⊗∘▵ {f = f}{g}{h}{k} =
    begin
      (h ⊗ k) ∘ (f ▵ g)
    ≡⟨⟩
      (h ∘ exl ▵ k ∘ exr) ∘ (f ▵ g)
    ≈⟨ ▵∘ ⟩
      (h ∘ exl) ∘ (f ▵ g) ▵ (k ∘ exr) ∘ (f ▵ g)
    ≈⟨ ▵≈ assoc assoc ⟩
      h ∘ exl ∘ (f ▵ g) ▵ k ∘ exr ∘ (f ▵ g)
    ≈⟨ ▵≈ (∘≈ʳ exl∘▵) (∘≈ʳ exr∘▵) ⟩
      h ∘ f ▵ k ∘ g
    ∎

open Cartesian ⦃ … ⦄ public

record CartesianClosed {obj : Set o} ⦃ _ : Products obj ⦄
                       ⦃ _ : Exponentials obj ⦄ (_⇨′_ : obj → obj → Set ℓ)
                       {q} ⦃ _ : Equivalent q _⇨′_ ⦄
                       ⦃ _ : Products (Set q) ⦄
                       ⦃ _ : R.Category _⇨′_ ⦄
                       ⦃ _ : R.Cartesian _⇨′_ ⦄
                       ⦃ _ : R.CartesianClosed _⇨′_ ⦄
                       ⦃ ⇨Category : Category _⇨′_ ⦄ ⦃ ⇨Cartesian : Cartesian _⇨′_ ⦄
       : Set (suc o ⊔ ℓ ⊔ suc q) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    ∀⇛ : ∀ {f : a × b ⇨ c} {g : a ⇨ (b ⇛ c)} → (g ≈ curry f) ⇔ (f ≈ uncurry g)
    -- Note: uncurry g ≡ apply ∘ first g ≡ apply ∘ (g ⊗ id)
    -- RHS is often written "apply ∘ (g ⊗ id)"

    curry≈ : ∀ {f g : a × b ⇨ c} → f ≈ g → curry f ≈ curry g

  ∀⇛→ : ∀ {f : a × b ⇨ c} {g : a ⇨ (b ⇛ c)}
      → g ≈ curry f → f ≈ uncurry g
  ∀⇛→ = to ∀⇛ ⟨$⟩_

  ∀⇛← : ∀ {f : a × b ⇨ c} {g : a ⇨ (b ⇛ c)}
      → f ≈ uncurry g → g ≈ curry f
  ∀⇛← = from ∀⇛ ⟨$⟩_

  curry-apply : ∀ {a b : obj} → id { a = a ⇛ b } ≈ curry apply
  curry-apply = ∀⇛← (begin
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
