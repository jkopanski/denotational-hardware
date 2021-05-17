{-# OPTIONS --safe --without-K #-}

-- Bit indices in values

module Log where

open import Level
open import Data.Empty
open import Data.Sum

open import Categorical.Object
open import Categorical.Equiv
open import Functions.Type 0ℓ
open import Ty

private variable a : Ty

Log : Ty → Set
Log `⊤ = ⊥
Log `Bool = ⊤
Log (a `× b) = Log a ⊎ Log b
Log (a `⇛ b) = Fₒ a × Log b

open import Data.Product using (_,_; curry; uncurry)
open import Function using (_∘_)

tabulate : (Log a → Bool) → Fₒ a
tabulate {  `⊤  } f = tt
tabulate {`Bool } f = f tt
tabulate {a `× b} f = tabulate (f ∘ inj₁) , tabulate (f ∘ inj₂)
tabulate {a `⇛ b} f = tabulate ∘ curry f

index : Fₒ a → (Log a → Bool)
index {  `⊤  }    tt   = λ ()
index {`Bool }    b    = λ { tt → b }
index {a `× b} (x , y) = [ index x , index y ]
index {a `⇛ b}    f    = uncurry (index ∘ f)
                         -- λ (x , j) → index (f x) j
