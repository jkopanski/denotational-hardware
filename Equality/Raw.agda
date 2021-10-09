{-# OPTIONS --safe --without-K #-}

module Equality.Raw {ℓ} {A : Set ℓ} where

open import Function using (flip)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Categorical.Raw

open import Equality.Type {ℓ} {A} public

module equality-raw where

 instance

  category : Category _⇨_
  category = record
    { id = ≡.refl
    ; _∘_ = flip ≡.trans
    }

  -- If we specialize A itself to Set a, I think we can give Cartesian and
  -- Cocartesian instances.
