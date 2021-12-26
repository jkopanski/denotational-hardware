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
  hasSemigroup ⦃ hrs ⦄ is-assoc = record { ∙-assoc = is-assoc }

record HasRawMonoid (A : Set a) ⦃ _ : HasRawSemigroup A ⦄ : Set a where
  field
    ι : A

open HasRawMonoid ⦃ … ⦄ public

record HasMonoid (A : Set a) ⦃ _ : HasRawSemigroup A ⦄ ⦃ _ : HasRawMonoid A ⦄ : Set a where
  field
    ∙-identityˡ : LeftIdentity  ι _∙_
    ∙-identityʳ : RightIdentity ι _∙_

open HasMonoid ⦃ … ⦄ public
