{-# OPTIONS --safe --without-K #-}

open import Level

open import Categorical.Raw
open import Categorical.Equiv
open import Categorical.Laws as L hiding (Category)
open import Categorical.Homomorphism

module Categorical.Comma.Homomorphism
   {o₁}{obj₁ : Set o₁} {ℓ₁}(_⇨₁_ : obj₁ → obj₁ → Set ℓ₁) ⦃ _ : Category _⇨₁_ ⦄
   {o₂}{obj₂ : Set o₂} {ℓ₂}(_⇨₂_ : obj₂ → obj₂ → Set ℓ₂) ⦃ _ : Category _⇨₂_ ⦄
   {o₃}{obj₃ : Set o₃} {ℓ₃}(_⇨₃_ : obj₃ → obj₃ → Set ℓ₃) ⦃ _ : Category _⇨₃_ ⦄
   q ⦃ _ : Equivalent q _⇨₁_ ⦄ ⦃ _ : Equivalent q _⇨₂_ ⦄ ⦃ _ : Equivalent q _⇨₃_ ⦄
   ⦃ _ : L.Category _⇨₃_ q ⦄
   ⦃ _ : Homomorphismₒ obj₁ obj₃ ⦄ ⦃ _ : Homomorphism _⇨₁_ _⇨₃_ ⦄
     ⦃ _ : CategoryH _⇨₁_ _⇨₃_ q ⦄
   ⦃ _ : Homomorphismₒ obj₂ obj₃ ⦄ ⦃ _ : Homomorphism _⇨₂_ _⇨₃_ ⦄
     ⦃ _ : CategoryH _⇨₂_ _⇨₃_ q ⦄
 where

open import Categorical.Comma.Raw _⇨₁_ _⇨₂_ _⇨₃_ q public

instance

  open import Categorical.Homomorphism

  categoryH₁ : CategoryH _⇨_ _⇨₁_ q
  categoryH₁ = record { F-id = refl ; F-∘ = refl }

  categoryH₂ : CategoryH _⇨_ _⇨₂_ q
  categoryH₂ = record { F-id = refl ; F-∘ = refl }

  -- Also CartesianH, CartesianClosedH, and LogicH
