{-# OPTIONS --safe --without-K #-}

open import Categorical.Homomorphism

module Linearize.Raw {o}{objₘ : Set o} ⦃ _ : Products objₘ ⦄ ⦃ _ : Exponentials objₘ ⦄
             {ℓₘ}(_⇨ₘ_ : objₘ → objₘ → Set ℓₘ) (let infix 0 _⇨ₘ_; _⇨ₘ_ = _⇨ₘ_)
             {ℓ}{obj : Set ℓ} ⦃ _ : Products obj ⦄ ⦃ _ : Exponentials obj ⦄
             (_⇨ₚ_ : obj → obj → Set ℓ) (let infix 0 _⇨ₚ_; _⇨ₚ_ = _⇨ₚ_)
             (_⇨ᵣ_ : obj → obj → Set ℓ) (let infix 0 _⇨ᵣ_; _⇨ᵣ_ = _⇨ᵣ_)
             ⦃ _ : CartesianClosed _⇨ₘ_ ⦄   -- monoidal suffices?
             ⦃ _ : Cartesian _⇨ᵣ_ ⦄   -- braided suffices
             -- The rest are for ⟦_⟧ₖ. Maybe move them into a submodule.
             ⦃ Hₒ : Homomorphismₒ obj objₘ ⦄
             ⦃ Hₚ : Homomorphism _⇨ₚ_ _⇨ₘ_ ⦄
             ⦃ Hᵣ : Homomorphism _⇨ᵣ_ _⇨ₘ_ ⦄
             {q} ⦃ _ : Equivalent q _⇨ₘ_ ⦄
             ⦃ _ : ProductsH obj _⇨ₘ_ ⦄ ⦃ _ : ExponentialsH obj _⇨ₘ_ ⦄
  where

private variable a b c d : obj

open import Linearize.Type _⇨ₘ_ _⇨ₚ_ _⇨ᵣ_ public

mutual

  ⟦_⟧ᵤ : (a ⇨ᵤ b) → (Fₒ a ⇨ₘ Fₒ b)
  ⟦ `prim p  ⟧ᵤ = Fₘ p
  ⟦ `curry f ⟧ᵤ = ν ∘ curry (⟦ f ⟧ₖ ∘ μ)
  ⟦ `apply   ⟧ᵤ = apply ∘ first ν⁻¹ ∘ μ⁻¹

  ⟦_⟧ₖ : (a ⇨ b) → (Fₒ a ⇨ₘ Fₒ b)
  ⟦ ⌞ r ⌟ ⟧ₖ = Fₘ r
  ⟦ f ∘·first u ∘ r ⟧ₖ = ⟦ f ⟧ₖ ∘ μ ∘ first ⟦ u ⟧ᵤ ∘ μ⁻¹ ∘ Fₘ r
                     -- ⟦ f ⟧ₖ ∘ first′ ⟦ u ⟧ᵤ ∘ Fₘ r

-- Types for curry & apply:
-- 
--              f        : a × b ⇨ c
--            ⟦ f ⟧ₖ      : Fₒ (a × b) ⇨ₘ Fₒ c
--            ⟦ f ⟧ₖ ∘ μ  : Fₒ a × Fₒ b ⇨ₘ Fₒ c
--     curry (⟦ f ⟧ₖ ∘ μ) : Fₒ a ⇨ₘ (Fₒ b ⇛ Fₒ c)
-- ν ∘ curry (⟦ f ⟧ₖ ∘ μ) : Fₒ a ⇨ₘ Fₒ (b ⇛ c)
-- 
--
-- apply                   : (Fₒ a ⇛ Fₒ b) × Fₒ a ⇨ₘ Fₒ b
-- apply ∘ first ν⁻¹       : Fₒ (a ⇛ b) × Fₒ a ⇨ₘ Fₒ b
-- apply ∘ first ν⁻¹ ∘ μ⁻¹ : Fₒ ((a ⇛ b) × a) ⇨ₘ Fₒ b

-- TODO: maybe move semantics to Type (for all categories in the project)

route : (a ⇨ᵣ b) → (a ⇨ b)
route = ⌞_⌟

primᵤ : (a ⇨ᵤ b) → (a ⇨ b)
primᵤ u = ⌞ unitorᵉʳ ⌟ ∘·first u ∘ unitorⁱʳ

prim : (a ⇨ₚ b) → (a ⇨ b)
prim p = primᵤ (`prim p)

infixr 9 _∘ₖ_
_∘ₖ_ : (b ⇨ c) → (a ⇨ b) → (a ⇨ c)
g ∘ₖ (f ∘·first u ∘ r) = (g ∘ₖ f) ∘·first u ∘ r
(g ∘·first u ∘ r₂) ∘ₖ ⌞ r₁ ⌟ = g ∘·first u ∘ (r₂ ∘ r₁)
⌞ r₂ ⌟ ∘ₖ ⌞ r₁ ⌟ = ⌞ r₂ ∘ r₁ ⌟

swapₖ : a × b ⇨ b × a
swapₖ = route swap

firstₖ : (a ⇨ c) → (a × b ⇨ c × b)
firstₖ ⌞ r ⌟ = ⌞ first r ⌟
firstₖ (f ∘·first u ∘ r) =
  (firstₖ f ∘ₖ ⌞ assocˡ ⌟) ∘·first u ∘ (assocʳ ∘ first r)

secondₖ : (b ⇨ d) → (a × b ⇨ a × d)
secondₖ f = swapₖ ∘ₖ firstₖ f ∘ₖ swapₖ

infixr 7 _⊗ₖ_
_⊗ₖ_ : (a ⇨ c) → (b ⇨ d) → (a × b ⇨ c × d)
f ⊗ₖ g = secondₖ g ∘ₖ firstₖ f

-- first (first f) ≈ assocˡ ∘ first f ∘ assocʳ

-- first (f ∘ first u ∘ r)
-- first f ∘ first (first u) ∘ first r
-- first f ∘ assocˡ ∘ first f ∘ assocʳ ∘ first r

-- TODO: when proofs are done, consider localizing _∘ₖ_, firstₖ, and secondₖ

instance

  homomorphism : Homomorphism _⇨_ _⇨ₘ_
  homomorphism = record { Fₘ = ⟦_⟧ₖ }

  category : Category _⇨_
  category = record { id = route id ; _∘_ = _∘ₖ_ }

  cartesian : Cartesian _⇨_
  cartesian = record { !   = route !
                     ; exl = route exl
                     ; exr = route exr
                     ; _▵_ = λ f g → (f ⊗ₖ g) ∘ route dup
                     }

  cartesianClosed : CartesianClosed _⇨_
  cartesianClosed = record
    { curry = λ f → primᵤ (`curry f)
    ; apply = primᵤ `apply
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

