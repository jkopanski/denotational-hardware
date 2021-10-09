{-# OPTIONS --safe --without-K #-}

module Equality.Type {ℓ} {A : Set ℓ} where

open import Relation.Binary.PropositionalEquality

infix 0 _⇨_
_⇨_ : A → A → Set ℓ
_⇨_ = _≡_
