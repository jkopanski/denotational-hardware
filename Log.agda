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

private variable a b : Ty

Log : Ty → Set
Log `⊤ = ⊥
Log `Bool = ⊤
Log (a `× b) = Log a ⊎ Log b
Log (a `⇛ b) = Fₒ a × Log b

open import Data.Product using (_,_; curry; uncurry)
open import Function using (_∘_)

lookup : Fₒ a → (Log a → Bool)
lookup {`Bool } b tt    = b
lookup {a `× b} (x , y) = [ lookup x , lookup y ]′
lookup {a `⇛ b} f       = uncurry (lookup ∘ f)
                          -- λ (x , j) → lookup (f x) j

tabulate : (Log a → Bool) → Fₒ a
tabulate {  `⊤  } f = tt
tabulate {`Bool } f = f tt
tabulate {a `× b} f = tabulate (f ∘ inj₁) , tabulate (f ∘ inj₂)
tabulate {a `⇛ b} f = tabulate ∘ curry f

-- open import Data.Fin

-- logFin : Log a → Fin (size a)
-- logFin {  `⊤  } = λ ()
-- logFin {`Bool } = λ { tt → Fin.zero }
-- logFin {a `× b} = [ inject+ _ ∘ logFin , raise _ ∘ logFin ]
-- logFin {a `⇛ b} = λ (x , j) → {!!}

-- Goal : Fin (size b * card a)

-- x : Fₒ a
-- j : Log b


-- logFin j : Fin (size b)
-- toFin : Fₒ a → Fin (card a)

