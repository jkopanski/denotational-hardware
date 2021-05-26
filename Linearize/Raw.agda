{-# OPTIONS --safe --without-K #-}

open import Categorical.Raw

module Linearize.Raw {ℓₘ}{objₘ : Set ℓₘ} ⦃ _ : Products objₘ ⦄
             (_⇨ₘ_ : objₘ → objₘ → Set ℓₘ) (let infix 0 _⇨ₘ_; _⇨ₘ_ = _⇨ₘ_)
             {ℓ}{obj : Set ℓ} ⦃ _ : Products obj ⦄
             (_⇨ₚ_ : obj → obj → Set ℓ) (let infix 0 _⇨ₚ_; _⇨ₚ_ = _⇨ₚ_)
             (_⇨ᵣ_ : obj → obj → Set ℓ) (let infix 0 _⇨ᵣ_; _⇨ᵣ_ = _⇨ᵣ_)
             ⦃ _ : Cartesian _⇨ₘ_ ⦄   -- monoidal suffices?
             ⦃ _ : Cartesian _⇨ᵣ_ ⦄   -- braided suffices
             -- The rest are for ⟦_⟧ₖ
             ⦃ Hₒ : Homomorphismₒ obj objₘ ⦄
             ⦃ Hₚ : Homomorphism _⇨ₚ_ _⇨ₘ_ ⦄
             ⦃ Hᵣ : Homomorphism _⇨ᵣ_ _⇨ₘ_ ⦄
             ⦃ _ : ProductsH obj _⇨ₘ_ ⦄
  where

private variable a b c d : obj

open import Linearize.Type _⇨ₘ_ _⇨ₚ_ _⇨ᵣ_ public

⟦_⟧ₖ : (a ⇨ b) → (Fₒ a ⇨ₘ Fₒ b)
⟦ ⌞ r ⌟ ⟧ₖ = Fₘ r
⟦ f ∘·first p ∘ r ⟧ₖ = ⟦ f ⟧ₖ ∘ μ ∘ first (Fₘ p) ∘ μ⁻¹ ∘ Fₘ r

route : (a ⇨ᵣ b) → (a ⇨ b)
route = ⌞_⌟

prim : (a ⇨ₚ b) → (a ⇨ b)
prim p = ⌞ unitorᵉʳ ⌟ ∘·first p ∘ unitorⁱʳ

infixr 9 _∘ₖ_
_∘ₖ_ : (b ⇨ c) → (a ⇨ b) → (a ⇨ c)
g ∘ₖ (f ∘·first p ∘ r) = (g ∘ₖ f) ∘·first p ∘ r
(g ∘·first p ∘ r₂) ∘ₖ ⌞ r₁ ⌟ = g ∘·first p ∘ (r₂ ∘ r₁)
⌞ r₂ ⌟ ∘ₖ ⌞ r₁ ⌟ = ⌞ r₂ ∘ r₁ ⌟

swapₖ : a × b ⇨ b × a
swapₖ = route swap

firstₖ : (a ⇨ c) → (a × b ⇨ c × b)
firstₖ ⌞ r ⌟ = ⌞ first r ⌟
firstₖ (f ∘·first p ∘ r) =
  (firstₖ f ∘ₖ ⌞ assocˡ ⌟) ∘·first p ∘ (assocʳ ∘ first r)

secondₖ : (b ⇨ d) → (a × b ⇨ a × d)
secondₖ f = swapₖ ∘ₖ firstₖ f ∘ₖ swapₖ

infixr 7 _⊗ₖ_
_⊗ₖ_ : (a ⇨ c) → (b ⇨ d) → (a × b ⇨ c × d)
f ⊗ₖ g = secondₖ g ∘ₖ firstₖ f

-- first (first f) ≈ assocˡ ∘ first f ∘ assocʳ

-- first (f ∘ first p ∘ r)
-- first f ∘ first (first p) ∘ first r
-- first f ∘ assocˡ ∘ first f ∘ assocʳ ∘ first r

-- TODO: when proofs are done, consider localizing _∘ₖ_, firstₖ, and secondₖ

instance

  category : Category _⇨_
  category = record { id = route id ; _∘_ = _∘ₖ_ }

  cartesian : Cartesian _⇨_
  cartesian = record { !   = route !
                     ; exl = route exl
                     ; exr = route exr
                     ; _▵_ = λ f g → (f ⊗ₖ g) ∘ route dup
                     }

  logic : ⦃ _ : Boolean obj ⦄ ⦃ _ : Logic _⇨ₚ_ ⦄ → Logic _⇨_
  logic = record
            { false = prim false
            ; true  = prim true
            ; not   = prim not
            ; ∧     = prim ∧
            ; ∨     = prim ∨
            ; xor   = prim xor
            ; cond  = prim cond
            }

  homomorphism : Homomorphism _⇨_ _⇨ₘ_
  homomorphism = record { Fₘ = ⟦_⟧ₖ }

  -- TODO: CategoryH, CartesianH, etc.

