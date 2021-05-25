{-# OPTIONS --safe --without-K #-}

module Fun.Raw where

open import Level

open import Categorical.Raw
open import Categorical.Equiv

open import Functions.Raw
open import Ty
open import Fun.Type public

module typed-instances where

  instance

    open import Function using (_on_)
    import Relation.Binary.Construct.On as On

    equivalent : Equivalent 0ℓ _⇨_
    equivalent = record { equiv = On.isEquivalence unMk equiv }

    -- equivalent =
    --   record { equiv = λ {a b} → On.isEquivalence unMk (isEquivₜ {a ⇛ b}) }

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
