{-# OPTIONS --safe --without-K #-}
-- Some convenient instances

module Functions.Instances (ℓ) where

open import Categorical.Homomorphism
open import Functions ℓ

instance

  Hₒ : Homomorphismₒ (Set ℓ) (Set ℓ)
  Hₒ = id-Hₒ

  pH : ProductsH (Set ℓ) Function
  pH = id-ProductsH

  H : Homomorphism Function Function
  H = id-H

  catH : CategoryH Function Function
  catH = id-CategoryH

  spH : StrongProductsH (Set ℓ) Function
  spH = id-StrongProductsH

  cartH : CartesianH Function Function
  cartH = id-CartesianH
