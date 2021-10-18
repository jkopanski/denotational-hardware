{-# OPTIONS --safe --without-K #-}
module Finite.Raw where

open import Level using (0ℓ)
import Function as F
open import Data.Nat
open import Data.Fin renaming (Fin to 𝔽) hiding (_+_)

open import Categorical.Raw

open import Functions.Raw 0ℓ

open import Finite.Type public

module finite-raw-instances where
 
  instance

    category : Category _⇨_
    category = record { id = mk id ; _∘_ = λ (mk g) (mk f) → mk (g ∘ f) }

    products : Products ℕ
    products = record { ⊤ = 1 ; _×_ = _*_ }

    cartesian : Cartesian _⇨_
    cartesian = record
      { !   = mk λ _ → zero
      ; _▵_ = λ (mk f) (mk g) → mk (λ i → combine (f i) (g i))
      ; exl = λ {m}{n} → mk (exl ∘ remQuot {m} n)
      ; exr = λ {m}{n} → mk (exr ∘ remQuot {m} n)
      }
