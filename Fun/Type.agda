{-# OPTIONS --safe --without-K #-}

module Fun.Type where

open import Categorical.Object
open import Categorical.Equiv

open import Functions.Type
open import Ty

infix 0 _⇨_
record _⇨_ (a b : Ty) : Set where
  constructor mk
  field
    unMk : Fₒ a  → Fₒ b  -- or ⟦ a ⇛ b ⟧

open _⇨_ public



