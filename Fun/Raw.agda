{-# OPTIONS --safe --without-K #-}

module Fun.Raw where

open import Categorical.Raw

open import Function using (_∘′_) renaming (id to id′)
open import Data.Unit renaming (tt to tt′)
open import Data.Product as × using (proj₁; proj₂; <_,_>; _,_)
import Data.Bool as B

open import Ty
open import Fun.Type public

module typed-instances where

  instance

    category : Category _⇨_
    category = record { id = mk id′ ; _∘_ = λ (mk g) (mk f) → mk (g ∘′ f) }

    cartesian : Cartesian _⇨_
    cartesian = record { !   = mk λ _ → tt′
                       ; exl = mk proj₁
                       ; exr = mk proj₂
                       ; _▵_ = λ (mk f) (mk g) → mk < f , g >
                       }

    cartesianClosed : CartesianClosed _⇨_
    cartesianClosed = record { curry = λ (mk f) → mk (×.curry f)
                             ; apply = mk λ (f , x) → f x
                             }

    logic : Logic _⇨_
    logic = record
              { false = mk λ tt → B.false
              ; true  = mk λ tt → B.true
              ; not   = mk B.not
              ; ∧     = mk (×.uncurry B._∧_)
              ; ∨     = mk (×.uncurry B._∨_)
              ; xor   = mk (×.uncurry B._xor_)
              ; cond  = mk λ (c , t , e) → B.if c then t else e
              }
