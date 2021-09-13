{-# OPTIONS --safe --without-K #-}
-- Free category

open import Categorical.Object

module Categorical.Free.Type where

open import Ty

private variable a b c d : Ty

infix  0 _⇨_
infixr 7 _`▵_
infixr 9 _`∘_

data _⇨_ : Ty → Ty → Set where
  `id  : a ⇨ a
  _`∘_ : (b ⇨ c) → (a ⇨ b) → (a ⇨ c)
  `!   : a ⇨ ⊤
  _`▵_ : (a ⇨ c) → (a ⇨ d) → (a ⇨ c × d)
  `exl : a × b ⇨ a
  `exr : a × b ⇨ b
  `false `true : ⊤ ⇨ Bool
  `not : Bool ⇨ Bool
  `∧ `∨ `xor : Bool × Bool ⇨ Bool
  `cond : Bool × (a × a) ⇨ a
