{-# OPTIONS --safe --without-K #-}
-- Algebraic structures with instances

-- In contrast to agda-stdlib's Algebra.*, these algebraic structures use
-- implicitly quantified laws and are meant for automatic instance selection.
-- I also swapped *-distribˡ and *-distribʳ for consistency with other names.

module HasAlgebra where

open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_)

private variable
  a : Level
  A : Set a

record HasRawSemigroup (A : Set a) : Set a where
  infixl 7 _∙_
  field
    _∙_ : A → A → A

open HasRawSemigroup ⦃ … ⦄ public

record HasSemigroup (A : Set a) ⦃ _ : HasRawSemigroup A ⦄ : Set a where
  field
    ∙-assoc : {x y z : A} → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

open HasSemigroup ⦃ … ⦄ public

record HasRawMonoid (A : Set a) ⦃ _ : HasRawSemigroup A ⦄ : Set a where
  field
    ι : A

open HasRawMonoid ⦃ … ⦄ public

record HasMonoid (A : Set a)
    ⦃ _ : HasRawSemigroup A ⦄ ⦃ _ : HasRawMonoid A ⦄ : Set a where
  field
    ∙-identityˡ : {y : A} → ι ∙ y ≡ y
    ∙-identityʳ : {x : A} → x ∙ ι ≡ x

open HasMonoid ⦃ … ⦄ public


record HasRawSemiring (A : Set a) : Set a where
  infixl 6 _+_
  infixl 7 _*_
  field
    0# 1# : A
    _+_ _*_ : A → A → A

open HasRawSemiring ⦃ … ⦄ public

record HasSemiring (A : Set a) ⦃ _ : HasRawSemiring A ⦄ : Set a where
  field
    -- Additive monoid
    +-assoc : {x y z : A} → (x + y) + z ≡ x + (y + z)
    +-identityˡ : {y : A} → 0# + y ≡ y
    +-identityʳ : {x : A} → x + 0# ≡ x
    -- Multiplicative monoid
    *-assoc : {x y z : A} → (x * y) * z ≡ x * (y * z)
    *-identityˡ : {y : A} → 1# * y ≡ y
    *-identityʳ : {x : A} → x * 1# ≡ x
    -- Connection (distributivity) 
    *-distribˡ : {x y z : A} → (x + y) * z ≡ x * z + y * z
    *-distribʳ : {x y z : A} → x * (y + z) ≡ x * y + x * z
    *-zeroˡ : {y : A} → 0# * y ≡ 0#
    *-zeroʳ : {x : A} → x * 0# ≡ 0#

open HasSemiring ⦃ … ⦄ public
