{-# OPTIONS --safe --without-K #-}

open import Level

module Functions.Raw (ℓ : Level) where

import Function as F
open import Data.Product as × using (_,_; proj₁; proj₂; <_,_>)
import Data.Bool as B

open import Categorical.Raw
open import Categorical.Equiv

open import Functions.Type ℓ public

module →-raw-instances where

  instance

    category : Category Function
    category = record { id = F.id ; _∘_ = F._∘′_ }

    cartesian : Cartesian Function
    cartesian = record { _▵_ = <_,_> ; exl = proj₁ ; exr = proj₂ }

    cartesianClosed : CartesianClosed Function
    cartesianClosed = record { curry = ×.curry ; apply = ×.uncurry id }

    logic : Logic Function
    logic = record
              { false = λ tt → 𝕗
              ; true  = λ tt → 𝕥
              ; not   = lift₁ B.not
              ; ∧     = uncurry (lift₂ B._∧_)
              ; ∨     = uncurry (lift₂ B._∨_)
              ; xor   = uncurry (lift₂ B._xor_)
              ; cond  = λ (lift c , e , t) → B.if c then t else e
              }

    open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_)

    -- TODO: move to Relation.Binary.PropositionalEquality.Properties as a PR
    equivalent : Equivalent ℓ Function
    equivalent = record
      { _≈_ = _≗_
      ; equiv = record
          { refl  = λ _ → ≡.refl
          ; sym   = λ f∼g x → ≡.sym (f∼g x)
          ; trans = λ f∼g g∼h x → ≡.trans (f∼g x) (g∼h x)
          }
      }

    -- Experiment. If we're about to copy this pattern, instead define a
    -- parametrized module that can be imported publicly.
    open import Categorical.Homomorphism
    Hₒ : Homomorphismₒ (Set ℓ) (Set ℓ)
    Hₒ = id-Hₒ
    H : Homomorphism Function Function
    H = id-H
    catH : CategoryH Function Function
    catH = id-CategoryH
