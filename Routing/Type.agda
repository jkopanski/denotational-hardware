{-# OPTIONS --safe --without-K #-}

module Routing.Type where

open import Level using (0ℓ)
open import Data.Empty
open import Data.Sum
open import Data.Product using (_,_)

open import Categorical.Raw
open import Functions.Raw
open import Fun.Type renaming (_⇨_ to _⇨ₜ_)

open import Ty
open import Index

Swizzle : Ty → Ty → Set  -- Rel Ty 0ℓ
Swizzle a b = ∀ {z} → Index z b → Index z a

swizzle : ∀ {a b} → Swizzle a b → (Fₒ a → Fₒ b)
swizzle r a = tabulate (lookup a ∘ r)

infix 0 _⇨_
record _⇨_ (a b : Ty) : Set where
  constructor mk
  field
    f : Swizzle a b

instance

  homomorphism : Homomorphism _⇨_ _⇨ₜ_ ⦃ Hₒ = id-Hₒ ⦄
  homomorphism = record { Fₘ = λ (mk r) → mk (swizzle r) }

  -- TODO: I think we'll want to use inductive extensional equality

  -- TODO: Generalize routing to any target category with Ty as objects. Later
  -- to any Cartesian category.

