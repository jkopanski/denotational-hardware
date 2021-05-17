{-# OPTIONS --safe --without-K #-}

open import Level

module Functions.Raw (o : Level) where

import Function as F
open import Data.Product as × using (_,_; proj₁; proj₂; <_,_>)
import Data.Bool as B

open import Categorical.Raw

open import Functions.Type o public

private

  variable A B C : Set

  lift→₀ : A → (⊤ → Lift o A)
  lift→₀ a tt = lift a

  lift→₁ : (A → B) → (Lift o A → Lift o B)
  lift→₁ f (lift x) = lift (f x)

  lift→₂ : (A → B → C) → (Lift o A × Lift o B → Lift o C)
  lift→₂ f (lift x , lift y) = lift (f x y)

module →-raw-instances where

  instance

    category : Category Function
    category = record { id = F.id ; _∘_ = F._∘′_ }

    cartesian : Cartesian Function
    cartesian = record { exl = proj₁ ; exr = proj₂ ; _▵_ = <_,_> }

    cartesianClosed : CartesianClosed Function
    cartesianClosed = record { curry = ×.curry ; apply = λ (f , a) → f a }

    logic : Logic Function
    logic = record
              { ∧     = lift→₂ B._∧_
              ; ∨     = lift→₂ B._∨_
              ; xor   = lift→₂ B._xor_
              ; not   = lift→₁ B.not
              ; true  = lift→₀ B.true
              ; false = lift→₀ B.false
              ; cond  = λ (lift c , (a , b)) → B.if c then b else a
              }

