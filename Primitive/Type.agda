{-# OPTIONS --safe --without-K #-}

-- Symbolic logic primitives
module Primitive.Type where

open import Ty

infix 0 _⇨_
data _⇨_ : Ty → Ty → Set where
  `false `true : `⊤ ⇨ `Bool
  `not : `Bool ⇨ `Bool
  `∧ `∨ `xor : `Bool `× `Bool ⇨ `Bool
  `cond : ∀ {a} → `Bool `× (a `× a) ⇨ a


module primitive-type-instance where

  instance

    open import Show
    open import Data.String

    show′ : ∀ {a b} → Show (a ⇨ b)
    show′ = record { show = λ { `false → "false"
                              ; `true  → "true"
                              ; `not   → "not"
                              ; `∧     → "∧"
                              ; `∨     → "∨"
                              ; `xor   → "⊕"
                              ; `cond  → "cond"
                              }
                   }
