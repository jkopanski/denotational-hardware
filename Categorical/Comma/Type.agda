{-# OPTIONS --safe --without-K #-}

open import Level

open import Categorical.Raw
open import Categorical.Equiv
open import Categorical.Homomorphism

module Categorical.Comma.Type
   {o₁}{obj₁ : Set o₁} {ℓ₁}(_⇨₁_ : obj₁ → obj₁ → Set ℓ₁) ⦃ _ : Category _⇨₁_ ⦄
   {o₂}{obj₂ : Set o₂} {ℓ₂}(_⇨₂_ : obj₂ → obj₂ → Set ℓ₂) ⦃ _ : Category _⇨₂_ ⦄
   {o₃}{obj₃ : Set o₃} {ℓ₃}(_⇨₃_ : obj₃ → obj₃ → Set ℓ₃) ⦃ _ : Category _⇨₃_ ⦄
   q ⦃ _ : Equivalent q _⇨₃_ ⦄
   ⦃ _ : Homomorphismₒ obj₁ obj₃ ⦄ ⦃ _ : Homomorphism _⇨₁_ _⇨₃_ ⦄
     ⦃ _ : CategoryH _⇨₁_ _⇨₃_ q ⦄
   ⦃ _ : Homomorphismₒ obj₂ obj₃ ⦄ ⦃ _ : Homomorphism _⇨₂_ _⇨₃_ ⦄
     ⦃ _ : CategoryH _⇨₂_ _⇨₃_ q ⦄
 where

-- TODO: Define some bundles to reduce syntactic clutter.

record Obj : Set (o₁ ⊔ o₂ ⊔ ℓ₃) where
  constructor mk
  field
    { τ₁ } : obj₁
    { τ₂ } : obj₂
    h : Fₒ τ₁ ⇨₃ Fₒ τ₂

infix 0 _⇨_
record _⇨_ (a : Obj) (b : Obj) : Set (q ⊔ ℓ₁ ⊔ ℓ₂) where
  constructor mk
  open Obj
  field
    f₁ : τ₁ a ⇨₁ τ₁ b
    f₂ : τ₂ a ⇨₂ τ₂ b
    commute : Fₘ f₂ ∘ h a ≈ h b ∘ Fₘ f₁
