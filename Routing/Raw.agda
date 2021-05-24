{-# OPTIONS --safe --without-K #-}

module Routing.Raw where

open import Level using (0ℓ)
open import Data.Product using (_,_)
import Data.Sum as ⊎
open ⊎

open import Categorical.Raw
open import Functions.Raw

import Ty  -- For Products Ty
open import Index
open import Routing.Type public

instance

  category : Category _⇨_
  category = record { id = mk id ; _∘_ = λ (mk g) (mk f) → mk (f ∘ g) }

  cartesian : Cartesian _⇨_
  cartesian = record
    { !   = mk λ ()
    ; exl = mk left
    ; exr = mk right
    ; _▵_ = λ (mk f) (mk g) → mk λ { (left i) → f i ; (right j) → g j }
    }

  -- categoryH : CategoryH _⇨_ Function 0ℓ
  -- categoryH = ?
