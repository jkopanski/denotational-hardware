{-# OPTIONS --safe --without-K #-}
module Finite.Raw where

open import Level using (0ℓ)
open import Function using (flip)
open import Data.Nat
open import Data.Fin renaming (Fin to 𝔽) hiding (_+_)
-- open import Data.Product using (_,_)

open import Categorical.Raw

open import Functions.Raw 0ℓ

open import Finite.Type public
-- open import Finite.Fun

-- TODO: The cartesian closed functor instance.

module finite-raw-instances where
 
  instance

    category : Category _⇨_
    category = record { id = mk id ; _∘_ = λ (mk g) (mk f) → mk (g ∘ f) }

    products : Products ℕ
    products = record { ⊤ = 1 ; _×_ = _*_ }

    open import Data.Product using (_,_)
    cartesian : Cartesian _⇨_
    cartesian = record
      { !   = mk λ _ → zero
      ; _▵_ = λ (mk f) (mk g) → mk (uncurry combine ∘ (f ▵ g))
                                -- mk (λ i → uncurry combine (f i , g i))
                                -- mk (λ i → combine (f i) (g i))
      ; exl = λ {m}{n} → mk (exl ∘ remQuot {m} n)
      ; exr = λ {m}{n} → mk (exr ∘ remQuot {m} n)
      }

    exponentials : Exponentials ℕ
    exponentials = record { _⇛_ = flip _^_ }

    -- cartesianClosed : CartesianClosed _⇨_
    -- cartesianClosed = record
    --   { curry = λ (mk f) → {!!}
    --   ; apply = {!!}
    --   }
