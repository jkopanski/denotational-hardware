{-# OPTIONS --safe --without-K #-}

module Categorical.Equiv where

open import Level
open import Function using (_∘′_) renaming (id to id′)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidR

private
  variable
    o ℓ o₁ ℓ₁ o₂ ℓ₂ : Level
    obj : Set o
    a b : obj

record Equivalent q {obj : Set o} (_⇨_ : obj → obj → Set ℓ)
       : Set (o ⊔ ℓ ⊔ suc q) where
  infix 4 _≈_
  field
    _≈_ : Rel (a ⇨ b) q   -- (f g : a ⇨ b) → Set q
    equiv : IsEquivalence (_≈_ {a}{b})

  module Equiv {a b} where
    open IsEquivalence (equiv {a}{b}) public
      -- renaming (refl to refl≈; sym to sym≈; trans to trans≈)
  open Equiv public

  ≈setoid : obj → obj → Setoid ℓ q
  ≈setoid a b = record { isEquivalence = equiv {a}{b} }

  module ≈-Reasoning {a b} where
    open SetoidR (≈setoid a b) public

  infixr 9 _•_
  _•_ : {f g h : a ⇨ b} (g≈h : g ≈ h) (f≈g : f ≈ g) → f ≈ h
  g≈h • f≈g = trans f≈g g≈h

  -- Conflicts with other instances

-- TODO: Replace Equivalent by Setoid?
-- I think we need _⇨_ as an argument rather than field.

open Equivalent ⦃ … ⦄ public

-- TODO: consider moving to Categorical.Homomorphism.
record Homomorphismₒ (obj₁ : Set o₁) (obj₂ : Set o₂) : Set (o₁ ⊔ o₂) where
  field
    Fₒ : obj₁ → obj₂

open Homomorphismₒ ⦃ … ⦄ public

id-Hₒ : Homomorphismₒ obj obj
id-Hₒ = record { Fₒ = id′ }

record Homomorphism
  {obj₁ : Set o₁} (_⇨₁_ : obj₁ → obj₁ → Set ℓ₁)
  {obj₂ : Set o₂} (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂)
  ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
  : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂) where
  field
    Fₘ : (a ⇨₁ b) → (Fₒ a ⇨₂ Fₒ b)

open Homomorphism ⦃ … ⦄ public

import Relation.Binary.Construct.On as On

H-equiv : {obj₁ : Set o₁} {_⇨₁_ : obj₁ → obj₁ → Set ℓ₁}
          {obj₂ : Set o₂} {_⇨₂_ : obj₂ → obj₂ → Set ℓ₂}
          {q : Level} ⦃ _ : Equivalent q _⇨₂_ ⦄
          ⦃ _ : Homomorphismₒ obj₁ obj₂ ⦄
          (H : Homomorphism _⇨₁_ _⇨₂_)  -- note explicit/visible argument
        → Equivalent q _⇨₁_
H-equiv H = record { equiv = On.isEquivalence (Homomorphism.Fₘ H) equiv }
