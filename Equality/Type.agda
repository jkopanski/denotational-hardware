{-# OPTIONS --safe --without-K #-}

module Equality.Type {ℓ} {A : Set ℓ} where

open import Relation.Binary.PropositionalEquality

infix 0 _⇨_
record _⇨_ (x y : A) : Set ℓ where
  constructor mk
  field
    eq : x ≡ y
