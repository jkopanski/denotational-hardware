{-# OPTIONS --safe --without-K #-}

open import Level
open import Function using (id)
open import Data.Unit
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  renaming (refl to ≡-refl)

module Routing.Homomorphism where

open import Functions.Raw
open import Routing.Raw public
open import Ty
open import Index

open import Categorical.Homomorphism hiding (id)
open import Categorical.Laws

swizzle-id : (a : Ty) → swizzle {a = a} id ≈ id
swizzle-id `⊤         = ≡-refl
swizzle-id `Bool      = ≡-refl
swizzle-id (a₁ `⇛ a₂) = ≡-refl
swizzle-id (a₁ `× a₂) = cong₂ _,_ (swizzle-id a₁) (swizzle-id a₂)

lookup∘tabulate-id : {a : Ty}{f : Indexer Fₒ a} → ∀{z}{i : Index z a}
                   → lookup {a = a} (tabulate {a = a} f) i ≡ f i
lookup∘tabulate-id {f} = {!!}

swizzle-∘ : {b c a : Ty}{g : Swizzle b c}{f : Swizzle a b}
          → swizzle (f ∘ g) ≈ swizzle g ∘ swizzle f
-- Here I cannot use ≈-Reasoning because the implicit x is added to the
-- left hand side, so the goal is already of a different type.
swizzle-∘ {b} {c} {a} {g} {f} = {!!}
{-
   tabulate ((lookup x ∘ f) ∘ g)
  ≡⟨ ≡-refl ⟩
   tabulate (id (lookup x ∘ f) ∘ g)
  ≡⟨ {!!} ⟩ -- here I'd need function extensionality to prove id ≡ (lookup ∘ tabulate)
   tabulate (lookup (tabulate (lookup x ∘ f)) ∘ g)
  ≡⟨ ≡-refl ⟩
   swizzle g (tabulate (lookup x ∘ f))
  ∎
  where open ≡-Reasoning
-}

instance

  categoryH : CategoryH _⇨_ Function 0ℓ ⦃ Hₒ = ty-instances.homomorphismₒ ⦄
  categoryH = record
    { F-id = λ {a} → swizzle-id a
    ; F-∘ = {!!}
    }

{-

-- TODO:

-- Also CartesianH, CartesianClosedH, and LogicH

-}
