{-# OPTIONS --safe --without-K #-}

open import Categorical.Equiv
open import Categorical.Raw

module Typed.Type {o ℓ} {obj : Set o}
 ⦃ _ : Products obj ⦄ ⦃ _ : Exponentials obj ⦄ ⦃ _ : Boolean obj ⦄
 (_↠_ : obj → obj → Set ℓ) where

open import Data.Nat

open import Ty

private variable a b c d : Ty

infix 0 _⇨_
record _⇨_ (a b : Ty) : Set ℓ where
  constructor mk
  field
    f : Fₒ a ↠ Fₒ b
