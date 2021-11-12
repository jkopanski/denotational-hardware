{-# OPTIONS --safe --without-K #-}
-- Category of "finite sets", indexed by cardinality

module Finite where

open import Level using (0ℓ)
open import Data.Nat

open import Functions 0ℓ

module finite-instances where

open import Finite.Object public -- instances

-- Define the subcategory of ⟨→⟩ with homomorphisms and laws
open import Categorical.Subcategory ℕ ⟨→⟩ public

