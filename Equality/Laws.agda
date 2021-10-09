{-# OPTIONS --safe --without-K #-}

module Equality.Laws {ℓ} {A : Set ℓ} where

open import Function using (flip)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
import Relation.Binary.Construct.Always as A

open import Categorical.Equiv
open import Categorical.Raw
import Categorical.Laws as L

open import Equality.Raw {ℓ} {A} public

module equality-laws where

 instance

  equivalent : Equivalent ℓ _⇨_
  equivalent = record { _≈_ = A.Always }

  category : L.Category _⇨_
  category = _
