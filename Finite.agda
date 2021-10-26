{-# OPTIONS --safe --without-K #-}

module Finite where

open import Level using (0ℓ)
open import Data.Nat
open import Data.Fin

open import Categorical.Equiv
open import Categorical.Homomorphism hiding (uncurry)

open import Functions 0ℓ

module finite-instances where

  import Relation.Binary.PropositionalEquality as ≡
  open import Data.Fin.Properties
  open import Data.Product using (uncurry) -- for μ⁻¹∘μ

  instance

    Hₒ : Homomorphismₒ ℕ Set
    Hₒ = record { Fₒ = Fin }

    products : Products ℕ
    products = record { ⊤ = 1 ; _×_ = _*_ }

    productsH : ProductsH ℕ ⟨→⟩
    productsH = record
                  { ε     = λ { tt → zero }
                  ; μ     = uncurry combine
                  ; ε⁻¹   = λ { zero → tt }
                  ; μ⁻¹   = λ {m n} → remQuot n
                  ; ε⁻¹∘ε = λ { tt → ≡.refl }
                  ; ε∘ε⁻¹ = λ { zero → ≡.refl }
                  ; μ⁻¹∘μ = uncurry remQuot-combine
                  ; μ∘μ⁻¹ = λ {m n} → combine-remQuot {m} n
                  }
    -- TODO: Construct productsH from 1↔⊤ and *↔×
    -- TODO: Coproducts
    -- TODO: Exponentials

open import Categorical.Subcategory ⟨→⟩ ℕ public

