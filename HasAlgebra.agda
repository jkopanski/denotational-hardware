{-# OPTIONS --safe --without-K #-}
-- Algebraic structures with instances

-- In contrast to agda-stdlib's Algebra.*, these algebraic structures use
-- implicitly quantified laws and are meant for automatic instance selection. I
-- also swapped *-distribˡ and *-distribʳ for consistency with other identity
-- and zero properties.

module HasAlgebra where

open import Level using (Level)
open import Relation.Binary.PropositionalEquality renaming (trans to _;_)
open ≡-Reasoning

module _ {a} (A : Set a) where

  Bop : Set a
  Bop = A → A → A

  Assoc : Bop → Set a
  Assoc _∙_ = ∀ {x y z} → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

  Commutative : Bop → Set a
  Commutative _∙_ = ∀ {x y} → x ∙ y ≡ y ∙ x

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


  record HasRawMonoid : Set a where
    infixl 7 _∙_
    field
      ι : A
      _∙_ : Bop

  open HasRawMonoid ⦃ … ⦄ public

  record HasMonoid : Set a where
    field
      ⦃ raw ⦄ : HasRawMonoid
      ∙-identityˡ : Identityˡ _∙_ ι
      ∙-identityʳ : Identityʳ _∙_ ι
      ∙-assoc     : Assoc _∙_

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
      +-comm : Commutative _+_
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

  module monoid {_∙̂_ ι̂} (is : IsMonoid _∙̂_ ι̂) where
   instance
    has-raw-monoid : HasRawMonoid
    has-raw-monoid = record { ι = ι̂ ; _∙_ = _∙̂_ }

    has-monoid : HasMonoid
    has-monoid = record
      { ∙-assoc     = is.assoc _ _ _
      ; ∙-identityˡ = is.identityˡ _
      ; ∙-identityʳ = is.identityʳ _
      } where module is = IsMonoid is

  module semiring {_+̂_ _*̂_ 0̂ 1̂} (is : IsSemiring _+̂_ _*̂_ 0̂ 1̂) where
   instance
    has-raw-semiring : HasRawSemiring
    has-raw-semiring = record { 0# = 0̂ ; 1# = 1̂ ; _+_ = _+̂_ ; _*_ = _*̂_ }

    has-semiring : HasSemiring
    has-semiring = record
      { +-assoc     = is.+-assoc _ _ _
      ; +-identityˡ = is.+-identityˡ _
      ; +-identityʳ = is.+-identityʳ _
      ; +-comm      = is.+-comm _ _
      ; *-assoc     = is.*-assoc _ _ _
      ; *-identityˡ = is.*-identityˡ _
      ; *-identityʳ = is.*-identityʳ _
      ; *-distribˡ  = is.distribʳ _ _ _   -- note swap
      ; *-distribʳ  = is.distribˡ _ _ _
      ; *-zeroˡ     = is.zeroˡ _
      ; *-zeroʳ     = is.zeroʳ _
      } where module is = IsSemiring is

-- Some instances. WIP. How to make convenient?

module nat-algebra where
  open import Data.Nat.Properties
  open monoid   _ +-0-isMonoid   public
  open semiring _ +-*-isSemiring public

module ∧-algebra where
  open import Data.Bool.Properties
  open monoid _ ∧-isMonoid public

module ∨-algebra where
  open import Data.Bool.Properties
  open monoid _ ∨-isMonoid public


open import Data.Nat using (ℕ; zero; suc)


-- Oops: I found times etc below in Algebra.Definitions.RawMonoid and
-- Algebra.Properties.Monoid.Mult in agda-stdlib. I'll remove the redundant
-- functionality here.

module _ {a} {A : Set a} ⦃ _ : HasRawMonoid A ⦄ where
  -- What to call this one? For an additive interpretation, i'd like to use "0̂",
  -- "+", and "·".
  times : ℕ → A → A
  times zero x = ι
  times (suc n) x = x ∙ times n x

module _ where
  private
    timesℕ : ∀ m {n : ℕ} → times m n ≡ m * n
    timesℕ  zero   {n} = refl
    timesℕ (suc m) {n} = cong (n +_) (timesℕ m)

    -- timesℕ (suc m) {n} =
    --   begin
    --     times (suc m) n
    --   ≡⟨⟩
    --     n + times m n
    --   ≡⟨ cong (n +_) (timesℕ m) ⟩
    --     n + m * n
    --   ≡⟨⟩
    --     suc m * n
    --   ∎

  times-1 : ∀ {n} → times n 1 ≡ n
  times-1 {n} = timesℕ n ; *-identityʳ

module _ {a} {A : Set a} ⦃ _ : HasMonoid A ⦄ where

  times-distrib : ∀ m {n} {x : A} → times (m + n) x ≡ times m x ∙ times n x
  -- times-distrib  zero   = sym ∙-identityˡ
  times-distrib zero {n} {x} =
    begin
      times (zero + n) x
    ≡⟨⟩
      times n x
    ≡˘⟨ ∙-identityˡ ⟩
      ι ∙ times n x
    ≡⟨⟩
      times zero x ∙ times n x
    ∎
  times-distrib (suc m) {n} {x} =
    begin
      times (suc m + n) x
    ≡⟨⟩
      x ∙ times (m + n) x
    ≡⟨ cong (x ∙_) (times-distrib m) ⟩
      x ∙ (times m x ∙ times n x)
    ≡˘⟨ ∙-assoc ⟩
      (x ∙ times m x) ∙ times n x
    ≡⟨⟩
      times (suc m) x ∙ times n x
    ∎

  times-assoc : ∀ m {n} {x : A} → times (m * n) x ≡ times m (times n x)
  times-assoc zero = refl
  times-assoc (suc m) {n} {x} =
    begin
      times (suc m * n) x
    ≡⟨⟩
      times (n + m * n) x
    ≡⟨ times-distrib n ⟩
      times n x ∙ times (m * n) x
    ≡⟨ cong (times n x ∙_) (times-assoc m) ⟩
      times n x ∙ times m (times n x)
    ≡⟨⟩
      times (suc m) (times n x)
    ∎
