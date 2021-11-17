{-# OPTIONS --safe --without-K #-}
-- Free category

open import Categorical.Homomorphism
open import Categorical.Laws as L
       hiding (Category; Cartesian; CartesianClosed; Logic)

module Categorical.Free
   {o}{obj : Set o}
   ⦃ _ : Products obj ⦄ ⦃ _ : Exponentials obj ⦄ ⦃ _ : Boolean obj ⦄
   {ℓ}(_↠_ : obj → obj → Set ℓ) {q} ⦃ equiv↠ : Equivalent q _↠_ ⦄
   ⦃ _ : Category _↠_ ⦄ ⦃ _ : Cartesian _↠_ ⦄ ⦃ _ : Logic _↠_ ⦄
 where

open import Categorical.Free.Homomorphism public
