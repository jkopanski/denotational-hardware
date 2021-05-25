{-# OPTIONS --safe --without-K #-}

module Routing.Raw where

open import Level using (0ℓ)
open import Data.Product using (_,_)
import Data.Sum as ⊎
open ⊎

open import Categorical.Raw
open import Functions.Raw

open import Ty
open import Index
open import Fun.Raw renaming (_⇨_ to _⇨ₜ_)
open import Routing.Type public


open import Relation.Binary.PropositionalEquality renaming (refl to refl≡)
open import Categorical.Raw
open import Functions.Raw

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

swizzle-id : ∀ a {x : Fₒ a} → swizzle {b = a} id x ≡ x
swizzle-id `⊤       = refl≡
swizzle-id `Bool    = refl≡
swizzle-id (a `× b) = cong₂ _,_ (swizzle-id a) (swizzle-id b)
swizzle-id (a `⇛ b) = refl≡

-- Oh!! I don't need to use eqₜ in swizzle-id. Maybe I don't need eqₜ at all and
-- can use noninductive extensional equality.

instance

  categoryH : CategoryH _⇨_ _⇨ₜ_ 0ℓ ⦃ Hₒ = id-Hₒ ⦄
  categoryH = record
    { F-id = λ {a : Ty} (x : Fₒ a) → swizzle-id a
    ; F-∘  = λ g f → {!!}
    }
