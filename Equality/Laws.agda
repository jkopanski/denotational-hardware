{-# OPTIONS --safe --without-K #-}

module Equality.Laws {ℓ} (A : Set ℓ) where

open import Function using (flip)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Categorical.Equiv
open import Categorical.Raw
import Categorical.Laws as L

open import Equality.Raw A public

module equality-laws where

 instance

  category : L.Category _⇨_
  category = _
