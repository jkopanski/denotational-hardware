{-# OPTIONS --safe --without-K #-}
-- The category of functions on finite "sets" (Fin)

module Finite.Type where

open import Data.Nat
open import Data.Fin renaming (Fin to 𝔽)

infix 0 _⇨_

record _⇨_ (m n : ℕ) : Set where
  constructor mk
  field
    f : 𝔽 m → 𝔽 n

-- Alternatively, f : Vec m (𝔽 n)
