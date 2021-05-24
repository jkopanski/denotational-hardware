{-# OPTIONS --safe --without-K #-}

module Fun.Raw where

open import Level

open import Categorical.Raw

open import Functions.Raw
open import Ty
open import Fun.Type public

module typed-instances where

  instance

    category : Category _⇨_
    category = record { id = mk id ; _∘_ = λ (mk g) (mk f) → mk (g ∘ f) }

    cartesian : Cartesian _⇨_
    cartesian = record { ! = mk ! ; exl = mk exl ; exr = mk exr
                       ; _▵_ = λ (mk f) (mk g) → mk (f ▵ g) }

    cartesianClosed : CartesianClosed _⇨_
    cartesianClosed =
      record { curry = λ (mk f) → mk (curry f) ; apply = mk apply }

    logic : Logic _⇨_
    logic = record { false = mk false ; true = mk true
                   ; ∧ = mk ∧ ; ∨ = mk ∨ ; xor = mk xor ; not = mk not
                   ; cond = mk cond }
