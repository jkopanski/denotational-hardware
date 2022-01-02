{-# OPTIONS --safe --without-K #-}
-- Algebraic structures with instances

-- In contrast to agda-stdlib's Algebra.*, these algebraic structures use
-- implicitly quantified laws and are meant for automatic instance selection. I
-- also swapped *-distribˡ and *-distribʳ for consistency with other identity
-- and zero properties.

module HasAlgebra where

open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_)

module _ {a} (A : Set a) where

  Bop : Set a
  Bop = A → A → A

  Assoc : Bop → Set a
  Assoc _∙_ = ∀ {x y z} → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

  Identityˡ Identityʳ : Bop → A → Set a
  Identityˡ _∙_ ι = ∀ {y : A} → ι ∙ y ≡ y
  Identityʳ _∙_ ι = ∀ {x : A} → x ∙ ι ≡ x

  Distribˡ Distribʳ : Bop → Bop → Set a
  Distribˡ _*_ _+_ = ∀ {x y z} → (x + y) * z ≡ (x * z) + (y * z)
  Distribʳ _*_ _+_ = ∀ {x y z} → x * (y + z) ≡ (x * y) + (x * z)
  -- Note: swapped from agda-stdlib

  Zeroˡ Zeroʳ : Bop → A → Set a
  Zeroˡ _*_ 0# = ∀ {y} → 0# * y ≡ 0#
  Zeroʳ _*_ 0# = ∀ {x} → x * 0# ≡ 0#


  record HasRawSemigroup : Set a where
    infixl 7 _∙_
    field
      _∙_ : Bop

  open HasRawSemigroup ⦃ … ⦄ public

  record HasSemigroup ⦃ _ : HasRawSemigroup ⦄ : Set a where
    field
      ∙-assoc : Assoc _∙_

  open HasSemigroup ⦃ … ⦄ public

  record HasRawMonoid ⦃ _ : HasRawSemigroup ⦄ : Set a where
    field
      ι : A

  open HasRawMonoid ⦃ … ⦄ public

  record HasMonoid ⦃ _ : HasRawSemigroup ⦄ ⦃ _ : HasRawMonoid ⦄ : Set a where
    field
      ∙-identityˡ : Identityˡ _∙_ ι
      ∙-identityʳ : Identityʳ _∙_ ι

  open HasMonoid ⦃ … ⦄ public


  record HasRawSemiring : Set a where
    infixl 6 _+_
    infixl 7 _*_
    field
      0# 1# : A
      _+_ _*_ : Bop

  open HasRawSemiring ⦃ … ⦄ public

  record HasSemiring ⦃ _ : HasRawSemiring ⦄ : Set a where
    field
      -- Additive monoid
      +-assoc : Assoc _+_
      +-identityˡ : Identityˡ _+_ 0#
      +-identityʳ : Identityʳ _+_ 0#
      -- Multiplicative monoid
      *-assoc : Assoc _*_
      *-identityˡ : Identityˡ _*_ 1#
      *-identityʳ : Identityʳ _*_ 1#
      -- Connection (distributivity) 
      *-distribˡ : Distribˡ _*_ _+_
      *-distribʳ : Distribʳ _*_ _+_
      *-zeroˡ : Zeroˡ _*_ 0#
      *-zeroʳ : Zeroʳ _*_ 0#

  open HasSemiring ⦃ … ⦄ public

  -- Adapt algebraic structures from agda-stdlib

  open import Algebra.Structures (_≡_ {A = A}) public

  module semiring {_+̂_ _*̂_ 0̂ 1̂} (is : IsSemiring _+̂_ _*̂_ 0̂ 1̂) where
   instance
    hasRaw : HasRawSemiring
    hasRaw = record { 0# = 0̂ ; 1# = 1̂ ; _+_ = _+̂_ ; _*_ = _*̂_ }

    has : HasSemiring
    has = record
            { +-assoc     = is.+-assoc _ _ _
            ; +-identityˡ = is.+-identityˡ _
            ; +-identityʳ = is.+-identityʳ _
            ; *-assoc     = is.*-assoc _ _ _
            ; *-identityˡ = is.*-identityˡ _
            ; *-identityʳ = is.*-identityʳ _
            ; *-distribˡ  = is.distribʳ _ _ _   -- note swap
            ; *-distribʳ  = is.distribˡ _ _ _
            ; *-zeroˡ     = is.zeroˡ _
            ; *-zeroʳ     = is.zeroʳ _
            } where module is = IsSemiring is


module nat-algebra where
  open import Data.Nat.Properties
  open semiring _ +-*-isSemiring public
