{-# OPTIONS --safe --without-K #-}

module Routing.Raw where

open import Level using (0ℓ)
open import Data.Product using (_,_)
import Data.Sum as ⊎
open ⊎

open import Categorical.Raw
open import Functions.Type 0ℓ
open import Functions.Raw  0ℓ

open import Ty
open import Log
open import Routing.Type public

private variable a b c d : Ty

instance

  category : Category _⇨_
  category = record { id = mk id ; _∘_ = λ (mk g) (mk f) → mk (f ∘ g) }

  cartesian : Cartesian _⇨_
  cartesian = record { !   = mk λ ()
                     ; exl = mk inj₁
                     ; exr = mk inj₂
                     ; _▵_ = λ (mk f) (mk g) → mk [ f , g ]
                     }

  -- I think _⇨_ is closed but not cartesian closed, i.e., we can define the hom
  -- functor but not curry & apply. A consequence is that curry f and apply must
  -- be treated similarly to primitives when linearizing.
