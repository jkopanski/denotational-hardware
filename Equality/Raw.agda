{-# OPTIONS --safe --without-K #-}

module Equality.Raw {ℓ} {A : Set ℓ} where

open import Function using (flip)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Binary.Construct.Always

open import Categorical.Raw
open import Categorical.Equiv

open import Equality.Type {ℓ} {A} public

module equality-raw where

 instance

  category : Category _⇨_
  category = record { id = ≡.refl ; _∘_ = flip ≡.trans }

  equivalent : Equivalent ℓ _⇨_
  equivalent = record { _≈_ = Always }
