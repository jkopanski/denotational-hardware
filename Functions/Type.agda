{-# OPTIONS --safe --without-K #-}

module Functions.Type where

open import Data.Unit using () renaming (⊤ to ⊤′)
open import Data.Product using () renaming (_×_ to _×′_)

open import Categorical.Raw

import Data.Bool as B

Function : Set → Set → Set
Function a b = a → b

pattern 𝕗 = B.false
pattern 𝕥 = B.true

bool : ∀ {ℓ}{σ : Set ℓ} → σ → σ → B.Bool → σ
bool e t c = B.if_then_else_ c t e

module →-instances where

  instance

    products : Products Set
    products = record { ⊤ = ⊤′ ; _×_ = _×′_ }

    exponentials : Exponentials Set
    exponentials = record { _⇛_ = Function }

    boolean : Boolean Set
    boolean = record { Bool = B.Bool }
