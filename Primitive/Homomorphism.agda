{-# OPTIONS --safe --without-K #-}

open import Level

open import Categorical.Raw
open import Categorical.Equiv
open import Categorical.Homomorphism
open import Categorical.Laws as L hiding (Cartesian)
open import Ty

module Primitive.Homomorphism
    {o ℓ} {obj : Set o}
    ⦃ _ : Products obj ⦄ ⦃ _ : Exponentials obj ⦄ ⦃ _ : Boolean obj ⦄
    (_↠_ : obj → obj → Set ℓ) (let infix 0 _↠_; _↠_ = _↠_)
    ⦃ _ : Logic _↠_ ⦄
    {q : Level} ⦃ _ : Equivalent q _↠_ ⦄
    -- For logicH:
    ⦃ _ : Cartesian _↠_ ⦄ ⦃ _ : L.Cartesian _↠_ q ⦄
 where

open import Primitive.Raw _↠_ public

private variable a b c : obj

-- TODO: fill in (https://github.com/conal/agda-hardware/issues/6)

-- instance

--   logicH : LogicH _⇨_ _↠_ q
--   logicH = ?
