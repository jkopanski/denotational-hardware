{-# OPTIONS --safe --without-K #-}
-- Free category

open import Categorical.Raw

module Categorical.Free.Raw where

open import Ty

open import Categorical.Free.Type public

private variable a b c d : Ty

module free-raw-instances where

 instance

   category : Category _⇨_
   category = record { id = `id ; _∘_ = _`∘_ }

   cartesian : Cartesian _⇨_
   cartesian = record { ! = `! ; _▵_ = _`▵_ ; exl = `exl ; exr = `exr }

   logic : Logic _⇨_
   logic = record
             { false = `false
             ; true  = `true
             ; not   = `not
             ; ∧     = `∧
             ; ∨     = `∨
             ; xor   = `xor
             ; cond  = `cond
             }
