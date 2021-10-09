{-# OPTIONS --safe --without-K #-}

module Equality.Homomorphism {ℓ} {A : Set ℓ} where

open import Function using (flip)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; subst)
open import Relation.Binary.PropositionalEquality.Properties

open import Categorical.Raw
open import Categorical.Homomorphism
open import Functions.Raw

open import Equality.Raw {ℓ} {A} public

-- For any P : A → Set, P and subst P form a functor
module equality-homomorphism-subst (P : A → Set) where

 instance

   Hₒ : Homomorphismₒ A Set
   Hₒ = record { Fₒ = P }

   H : Homomorphism _⇨_ Function
   H = record { Fₘ = subst P  }

   categoryH : CategoryH _⇨_ Function
   categoryH = record
     { F-id = λ _ → ≡.refl
     ; F-∘  = λ { {f = x≡y} _ → ≡.sym (subst-subst x≡y) }
     }
