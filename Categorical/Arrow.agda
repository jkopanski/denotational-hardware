{-# OPTIONS --safe --without-K #-}

open import Level

open import Categorical.Raw
open import Categorical.Equiv
open import Categorical.Laws as L hiding (Category)
open import Categorical.Homomorphism

module Categorical.Arrow
   {o}{obj : Set o} {ℓ}(_⇨_ : obj → obj → Set ℓ) ⦃ c : Category _⇨_ ⦄
   q ⦃ _ : Equivalent q _⇨_ ⦄
   ⦃ _ : L.Category _⇨_ q ⦄
 where

open import Categorical.Comma.Type _⇨_ _⇨_ _⇨_ q
        ⦃ hₒ₁ = id-Hₒ ⦄ ⦃ h₁ = id-H ⦄ ⦃ ch₁ = id-CategoryH ⦄
        ⦃ hₒ₂ = id-Hₒ ⦄ ⦃ h₂ = id-H ⦄ ⦃ ch₂ = id-CategoryH ⦄
     public
