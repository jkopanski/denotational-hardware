{-# OPTIONS --safe --without-K #-}

-- Indices of values within values

module Index where

open import Level
open import Data.Unit
open import Data.Sum
open import Data.Product using (_,_)
open import Function using (_∘_)

open import Categorical.Object
open import Categorical.Equiv
open import Ty
open import Functions.Type
open import Fun.Type
open import Fun.Raw

private variable a b z : Ty

data Index : Ty → Ty → Set where
  bit   : Index Bool Bool
  fun   : Index (a ⇛ b) (a ⇛ b)
  left  : Index z a → Index z (a × b)
  right : Index z b → Index z (a × b)

Indexer : Ty → Set
Indexer a = ∀ {z : Ty} → Index z a → Fₒ z

lookup : Fₒ a → Indexer a
lookup b          bit    = b
lookup f          fun    = f
lookup (x , _) (left  i) = lookup x i
lookup (_ , y) (right j) = lookup y j

tabulate : Indexer a → Fₒ a
tabulate {  `⊤  } f = tt
tabulate {`Bool } f = f bit
tabulate {_ `× _} f = tabulate (f ∘ left) , tabulate (f ∘ right)
tabulate {_ `⇛ _} f = f fun
