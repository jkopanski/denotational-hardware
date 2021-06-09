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

swizzle-id : (a : Ty) (x : Fₒ a) → swizzle {a = a} id x ≡ x
swizzle-id `⊤         _ = ≡-refl
swizzle-id `Bool      _ = ≡-refl
swizzle-id (a₁ `⇛ a₂) _ = ≡-refl
swizzle-id (a₁ `× a₂) (x₁ , x₂) = cong₂ _,_ (swizzle-id a₁ x₁) (swizzle-id a₂ x₂)

lookup∘tabulate-id : {a : Ty}{f : Indexer Fₒ a} → ∀{z}{i : Index z a}
                   → lookup {a = a} (tabulate {a = a} f) i ≡ f i
lookup∘tabulate-id {f} = {!!}

swizzle-∘ : {b c : Ty} (a : Ty) {g : Swizzle b c} {f : Swizzle a b} (x : Fₒ a)
          → swizzle (f ∘ g) x ≡ (swizzle g ∘ swizzle f) x
swizzle-∘ {b} {c} a {g} {f} x =
  begin
   swizzle (f ∘ g) x
  ≡⟨ cong tabulate {!!} ⟩
   tabulate ((lookup x ∘ f) ∘ g)
  ≡⟨ {!!} ⟩
   {! tabulate (lookup (tabulate (lookup x ∘ f) ∘ g)) !}
  ≡⟨ {!!} ⟩
   swizzle g (tabulate (lookup x ∘ f))
  ≡⟨ ≡-refl ⟩
   swizzle g (swizzle f x)
  ∎
  where open ≡-Reasoning

instance

  categoryH : CategoryH _⇨_ Function 0ℓ ⦃ Hₒ = ty-instances.homomorphismₒ ⦄
  categoryH = record
    { F-id = λ {a} {x} → swizzle-id a x
    ; F-∘ = {!!}
    }

{-

-- TODO:

-- Also CartesianH, CartesianClosedH, and LogicH

-}
