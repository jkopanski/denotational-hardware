{-# OPTIONS --safe --without-K #-}
-- Algebraic structures with instances

module HasAlgebra where

open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_)

private variable
  a : Level
  A : Set a

module _ {A : Set a} where
  open import Algebra.Definitions (_≡_ {A = A})
    using (Associative; LeftIdentity; RightIdentity) public

record HasRawSemigroup (A : Set a) : Set a where
  infixl 7 _∙_
  field
    _∙_ : A → A → A

open HasRawSemigroup ⦃ … ⦄ public

record HasSemigroup (A : Set a) ⦃ _ : HasRawSemigroup A ⦄ : Set a where
  field
    ∙-assoc : Associative _∙_

open HasSemigroup ⦃ … ⦄ public

module _ where
  hasSemigroup : ⦃ hrs : HasRawSemigroup A ⦄
    (is-assoc : Associative _∙_) → HasSemigroup A
  hasSemigroup is-assoc = record { ∙-assoc = is-assoc }


record HasRawMonoid (A : Set a) ⦃ _ : HasRawSemigroup A ⦄ : Set a where
  field
    ι : A

open HasRawMonoid ⦃ … ⦄ public

record HasMonoid (A : Set a)
    ⦃ _ : HasRawSemigroup A ⦄ ⦃ _ : HasRawMonoid A ⦄ : Set a where
  field
    ∙-identityˡ : LeftIdentity  ι _∙_
    ∙-identityʳ : RightIdentity ι _∙_

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
