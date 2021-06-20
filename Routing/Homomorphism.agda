{-# OPTIONS --safe --without-K #-}

open import Level
open import Function using (id) renaming (_∘_ to _∙_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)

module Routing.Homomorphism where

open import Functions.Raw
open import Routing.Raw public
open import Ty
open import Index

open import Categorical.Homomorphism hiding (id)
open import Categorical.Laws

lookup∘tabulate : ∀{a}{f : Indexer Fₒ a} → ∀{z}(i : Index z a)
                → lookup (tabulate f) i ≡ f i
lookup∘tabulate bit       = ≡-refl
lookup∘tabulate fun       = ≡-refl
lookup∘tabulate (left  i) = lookup∘tabulate i
lookup∘tabulate (right j) = lookup∘tabulate j

tabulate∘lookup : {a : Ty}(x : Fₒ a) → tabulate {a = a} (lookup x) ≡ x
tabulate∘lookup {a = `⊤}    tt = ≡-refl
tabulate∘lookup {a = `Bool} _  = ≡-refl
tabulate∘lookup {a = a₁ `⇛ a₂} x = ≡-refl
tabulate∘lookup {a = a₁ `× a₂} (x₁ , x₂)
  = cong₂ _,_ (tabulate∘lookup {a₁} x₁) (tabulate∘lookup {a₂} x₂)

≈-tabulate : {a : Ty}{f g : Indexer Fₒ a} → (∀{z}(i : Index z a) → f i ≡ g i)
           → tabulate f ≡ tabulate g
≈-tabulate {`⊤}     f≈g = ≡-refl
≈-tabulate {`Bool}  f≈g = f≈g bit
≈-tabulate {_ `⇛ _} f≈g = f≈g fun
≈-tabulate {_ `× _} f≈g = cong₂ _,_ (≈-tabulate (f≈g ∙ left))
                                    (≈-tabulate (f≈g ∙ right))

lookup-swizzle-∘ : {b c a : Ty}(g : Swizzle b c)(f : Swizzle a b){x : Fₒ a}
                 → ∀{z}(i : Index z c)
                 → lookup (swizzle f x) (g i) ≡ lookup (tabulate (lookup x ∘ f ∘ g)) i
lookup-swizzle-∘ g f i = ≡-trans (lookup∘tabulate (g i)) (≡-sym (lookup∘tabulate i))

swizzle-id : (a : Ty) → swizzle {a = a} id ≈ id
swizzle-id `⊤       = ≡-refl
swizzle-id `Bool    = ≡-refl
swizzle-id (a `⇛ b) = ≡-refl
swizzle-id (a `× b) = cong₂ _,_ (swizzle-id a) (swizzle-id b)

swizzle-∘ : {b c a : Ty}(g : Swizzle b c)(f : Swizzle a b)
          → swizzle (f ∘ g) ≈ swizzle g ∘ swizzle f
swizzle-∘ g f {x} =
  begin
    swizzle (f ∘ g) x
  ≡⟨⟩
    tabulate ((lookup x ∘ f) ∘ g)
  ≡˘⟨ ≈-tabulate (λ i → ≡-trans (lookup-swizzle-∘ g f i) (lookup∘tabulate i)) ⟩
    tabulate (lookup (tabulate (lookup x ∘ f)) ∘ g)
  ≡⟨⟩
    (swizzle g ∘ swizzle f) x
  ∎
 where open ≡-Reasoning

lookup-left : {a b : Ty}{x : Fₒ a × Fₒ b} → ∀{z}(i : Index z a)
            → (lookup {a = a `× b} x ∘ left) i ≡ lookup (proj₁ x) i
lookup-left _ = ≡-refl

swizzle-left : {a b : Ty} → swizzle {a = a `× b} {b = a} left ≈ proj₁
swizzle-left {a} {b} {x = x₁ , x₂} =
  begin
    swizzle {a = a `× b} {b = a} left (x₁ , x₂)
  ≡⟨ ≈-tabulate (lookup-left {a = a} {b = b} {x = x₁ , x₂}) ⟩
    tabulate {a = a} (lookup x₁)
  ≡⟨ tabulate∘lookup {a = a} x₁ ⟩
    x₁
  ∎
 where open ≡-Reasoning


lookup-right : {a b : Ty}{x : Fₒ a × Fₒ b} → ∀{z}(i : Index z b)
             → (lookup {a = a `× b} x ∘ right) i ≡ lookup (proj₂ x) i
lookup-right _ = ≡-refl

swizzle-right : {a b : Ty} → swizzle {a = a `× b} {b = b} right ≈ proj₂
swizzle-right {a} {b} {x = x₁ , x₂} =
  begin
    swizzle {a = a `× b} {b = b} right (x₁ , x₂)
  ≡⟨ ≈-tabulate (lookup-right {a = a} {b = b} {x = x₁ , x₂}) ⟩
    tabulate {a = b} (lookup x₂)
  ≡⟨ tabulate∘lookup {a = b} x₂ ⟩
    x₂
  ∎
 where open ≡-Reasoning


instance

  categoryH : CategoryH _⇨_ Function 0ℓ
  categoryH = record
    { F-id = λ {a} → swizzle-id a
    ; F-∘  = λ { {g = mk g} {mk f} → swizzle-∘ g f }
    }

  cartesianH : CartesianH _⇨_ Function 0ℓ
  cartesianH = record
    { F-!   = ≡-refl
    ; F-exl = λ {a} {b} {x} → swizzle-left {a} {b} {x}
    ; F-exr = λ {a} {b} {x} → swizzle-right {a} {b} {x}
    ; F-▵   = ≡-refl
    }

  -- TODO: Also CartesianClosedH, and LogicH
