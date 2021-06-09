{-# OPTIONS --safe --without-K #-}

open import Level
open import Data.Unit
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  renaming (refl to ≡-refl)

module Routing.Homomorphism where

open import Functions.Raw
open import Routing.Raw public
open import Ty
open import Index

swizzle-id-lemma : (a : Ty) (x : toObj a) → swizzle {a = a} (λ y → y) x ≡ x
swizzle-id-lemma `⊤         _ = ≡-refl
swizzle-id-lemma `Bool      _ = ≡-refl
swizzle-id-lemma (a₁ `⇛ a₂) x = ≡-refl
swizzle-id-lemma (a₁ `× a₂) (x₁ , x₂)
  = cong₂ _,_ (swizzle-id-lemma a₁ x₁) (swizzle-id-lemma a₂ x₂)

swizzle-∘-lemma : {b c : Ty} (a : Ty) {g : b ⇨ c} {f : a ⇨ b} (x : toObj a) →
      swizzle (λ x₁ → unMk f (unMk g x₁)) x ≡
      swizzle (unMk g) (swizzle (unMk f) x)
swizzle-∘-lemma a x = {!!}

instance

  open import Categorical.Homomorphism

  categoryH : CategoryH _⇨_ Function 0ℓ ⦃ Hₒ = ty-instances.homomorphismₒ ⦄
  categoryH = record
    { F-id = λ { {a = a} {x = x} → swizzle-id-lemma a x }
    ; F-∘ = {!!}
    }

{-

-- TODO:

-- Also CartesianH, CartesianClosedH, and LogicH

-}
