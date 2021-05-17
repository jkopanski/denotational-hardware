{-# OPTIONS --safe --without-K #-}

open import Categorical.Raw

module Typed.Raw {o ℓ} {obj : Set o}
 ⦃ _ : Products obj ⦄ ⦃ _ : Exponentials obj ⦄ ⦃ _ : Boolean obj ⦄
 (_↠_ : obj → obj → Set ℓ) where

open import Data.Nat

open import Ty

open import Typed.Type _↠_ public

private variable a b c d : Ty

module typed-instances where

  instance

    category : ⦃ _ : Category _↠_ ⦄ → Category _⇨_
    category = record { id = mk id ; _∘_ = λ (mk g) (mk f) → mk (g ∘ f) }

    cartesian : ⦃ _ : Cartesian _↠_ ⦄ → Cartesian _⇨_
    cartesian = record { exl = mk exl
                       ; exr = mk exr
                       ; _▵_ = λ (mk f) (mk g) → mk (f ▵ g)
                       ; !   = mk !
                       }

    cartesianClosed : ⦃ _ : CartesianClosed _↠_ ⦄ → CartesianClosed _⇨_
    cartesianClosed = record { curry = λ (mk f) → mk (curry f)
                             ; apply = mk apply }

    boolean : Boolean Ty
    boolean = record { Bool = `Bool }

    logic : ⦃ _ : Logic _↠_ ⦄ → Logic ⦃ boolean = boolean ⦄ _⇨_
    logic = record { false = mk false ; true = mk true
                   ; ∧ = mk ∧ ; ∨ = mk ∨ ; xor = mk xor ; not = mk not
                   ; cond = mk cond
                   }
