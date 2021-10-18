{-# OPTIONS --safe --without-K #-}
module Finite.Homomorphism where

open import Level using (0ℓ)
import Function as F
open import Data.Product using (_,_)
open import Data.Nat
open import Data.Fin renaming (Fin to 𝔽) hiding (_+_)
open import Data.Fin.Properties
open import Relation.Binary.PropositionalEquality

open import Categorical.Raw
open import Categorical.Homomorphism

open import Functions.Raw 0ℓ

open import Finite.Raw public

module finite-homomorphism-instances where
 
 instance

   Hₒ : Homomorphismₒ ℕ Set
   Hₒ = record { Fₒ = 𝔽 }

   H : Homomorphism _⇨_ ⟨→⟩
   H = record { Fₘ = λ (mk f) → f }

   categoryH : CategoryH _⇨_ ⟨→⟩
   categoryH = record
     { F-id = λ i → _≡_.refl
     ; F-∘  = λ i → _≡_.refl 
     }

   productsH : ProductsH ℕ ⟨→⟩
   productsH = record
                 { ε = λ { tt → zero }
                 ; μ = uncurry combine
                 ; ε⁻¹ = λ { zero → tt }
                 ; μ⁻¹ = remQuot _
                 ; ε⁻¹∘ε = λ { tt → _≡_.refl }
                 ; ε∘ε⁻¹ = λ { zero → _≡_.refl }
                 ; μ⁻¹∘μ = λ { (x , y) → remQuot-combine x y }
                 ; μ∘μ⁻¹ = λ {m}{n} → combine-remQuot {m} n
                 }

   cartesianH : CartesianH _⇨_ ⟨→⟩
   cartesianH = record
     { F-! = λ i → _≡_.refl
     ; F-▵ = λ i → _≡_.refl
     ; F-exl = λ (i , j) → cong exl (remQuot-combine i j)
     ; F-exr = λ (i , j) → cong exr (remQuot-combine i j)
     }

   equivalent : Equivalent 0ℓ _⇨_
   equivalent = H-equiv H
