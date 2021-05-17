-- Symbolic/initial logic primitives with the unique Logic homomorphism to any
-- other Logic instance.

open import Level
open import Categorical.Raw

module Primitive.Raw
    {o ℓ} {obj : Set o}
    ⦃ _ : Products obj ⦄ ⦃ _ : Exponentials obj ⦄ ⦃ _ : Boolean obj ⦄
    (_↠_ : obj → obj → Set ℓ)
    ⦃ _ : Logic _↠_ ⦄
  where

open import Categorical.Equiv

open import Ty
open import Primitive.Type public

private variable a b : Ty

module primitive-instances where

  instance

    H : Homomorphism _⇨_ _↠_
    H = record { Fₘ = λ { `false → false
                        ; `true  → true
                        ; `not   → not
                        ; `∧     → ∧
                        ; `∨     → ∨
                        ; `xor   → xor
                        ; `cond  → cond
                        }
               }

    logic : Logic _⇨_
    logic = record { false = `false ; true = `true
                   ; not = `not ; ∧ = `∧ ; ∨ = `∨ ; xor = `xor ; cond = `cond}
