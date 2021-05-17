{-# OPTIONS --safe --without-K #-}

open import Level

module Functions.Type (o : Level) where

open import Function using (_∘′_; const) renaming (id to id′)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤′)
open import Data.Product using (_,_; proj₁; proj₂; uncurry)
  renaming (_×_ to _×′_)

open import Categorical.Raw

import Data.Bool as B

Function : Set o → Set o → Set o
Function a b = a → b

pattern 𝕗 = lift B.false
pattern 𝕥 = lift B.true

module →-instances where

  instance

    products : Products (Set o)
    products = record { ⊤ = ⊤′ ; _×_ = _×′_ }

    exponentials : Exponentials (Set o)
    exponentials = record { _⇛_ = Function }

    boolean : Boolean (Set o)
    boolean = record { Bool = Lift o B.Bool }
