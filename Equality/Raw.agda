{-# OPTIONS --safe --without-K #-}

module Equality.Raw {ℓ} {A : Set ℓ} where

open import Function using (flip)
import Relation.Binary.PropositionalEquality as ≡

open import Categorical.Raw

open import Equality.Type {ℓ} {A} public

module equality-raw where

 instance

  category : Category _⇨_
  category = record
    { id = mk ≡.refl
    ; _∘_ = λ { (mk y≡z) (mk x≡y) → mk (≡.trans x≡y y≡z) }
    }

  -- If we specialize A itself to Set a, I think we can give Cartesian and
  -- Cocartesian instances.
