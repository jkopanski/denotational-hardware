{-# OPTIONS --safe --without-K #-}

module Categorical.Raw where

open import Level
open import Function using (_∘′_)

open import Categorical.Object public
open import Categorical.Equiv  public

private
  variable
    o ℓ o₁ ℓ₁ o₂ ℓ₂ : Level
    obj obj₁ obj₂ : Set o
    a b c d e : obj
    a′ b′ c′ d′ e′ : obj

record Category {obj : Set o} (_⇨_ : obj → obj → Set ℓ) : Set (o ⊔ ℓ) where
  infixr 9 _∘_
  field
    id  : a ⇨ a
    _∘_ : (g : b ⇨ c) (f : a ⇨ b) → (a ⇨ c)

open Category ⦃ … ⦄ public


-- Category homomorphism (functor)
record CategoryH {obj₁ : Set o₁} (_⇨₁_ : obj₁ → obj₁ → Set ℓ₁)
                 {obj₂ : Set o₂} (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂)
                 q ⦃ _ : Equivalent q _⇨₂_ ⦄
                 ⦃ _ : Category _⇨₁_ ⦄
                 ⦃ _ : Category _⇨₂_ ⦄
                 ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
                 ⦃ H : Homomorphism _⇨₁_ _⇨₂_ ⦄
       : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  field
    F-id : Fₘ (id {_⇨_ = _⇨₁_}{a = a}) ≈ id
    F-∘  : ∀ (g : b ⇨₁ c) (f : a ⇨₁ b) → Fₘ (g ∘ f) ≈ Fₘ g ∘ Fₘ f

open CategoryH ⦃ … ⦄ public


record ProductsH
    (obj₁ : Set o₁) ⦃ _ : Products obj₁ ⦄
    {obj₂ : Set o₂} ⦃ _ : Products obj₂ ⦄ (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    : Set (o₁ ⊔ o₂ ⊔ ℓ₂) where
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    -- https://ncatlab.org/nlab/show/monoidal+functor
    ε : ⊤ ⇨₂ Fₒ ⊤
    μ : {a b : obj₁} → Fₒ a × Fₒ b ⇨₂ Fₒ (a × b)

    -- *Strong*
    ε⁻¹ : Fₒ ⊤ ⇨₂ ⊤
    μ⁻¹ : {a b : obj₁} → Fₒ (a × b) ⇨₂ Fₒ a × Fₒ b

open ProductsH ⦃ … ⦄ public

id-ProductsH : ∀ {obj : Set o} ⦃ _ : Products obj ⦄
                 {_⇨_ : obj → obj → Set ℓ} ⦃ _ : Category _⇨_ ⦄
             → ProductsH obj _⇨_ ⦃ Hₒ = id-Hₒ ⦄
id-ProductsH = record { ε = id ; μ = id ; ε⁻¹ = id ; μ⁻¹ = id }

record Cartesian {obj : Set o} ⦃ _ : Products obj ⦄
         (_⇨′_ : obj → obj → Set ℓ) : Set (o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  infixr 7 _▵_
  field
    ⦃ ⇨Category ⦄ : Category _⇨_
    !   : a ⇨ ⊤
    exl : a × b ⇨ a
    exr : a × b ⇨ b
    _▵_ : ∀ {a c d} → a ⇨ c → (a ⇨ d) → (a ⇨ c × d)

  dup : a ⇨ a × a
  dup = id ▵ id

  infixr 7 _⊗_
  _⊗_ : (a ⇨ c) → (b ⇨ d) → (a × b ⇨ c × d)
  f ⊗ g = f ∘ exl ▵ g ∘ exr

  first : a ⇨ c → a × b ⇨ c × b
  first f = f ⊗ id

  second : b ⇨ d → a × b ⇨ a × d
  second g = id ⊗ g

  unitorᵉˡ : ⊤ × a ⇨ a
  unitorᵉˡ = exr

  unitorᵉʳ : a × ⊤ ⇨ a
  unitorᵉʳ = exl

  unitorⁱˡ : a ⇨ ⊤ × a
  unitorⁱˡ = ! ▵ id

  unitorⁱʳ : a ⇨ a × ⊤
  unitorⁱʳ = id ▵ !

  assocˡ : a × (b × c) ⇨ (a × b) × c
  assocˡ = second exl ▵ exr ∘ exr

  assocʳ : (a × b) × c ⇨ a × (b × c)
  assocʳ = exl ∘ exl ▵ first exr

  inAssocˡ : ((a × b) × c ⇨ (a′ × b′) × c′) → (a × (b × c) ⇨ a′ × (b′ × c′))
  inAssocˡ f = assocʳ ∘ f ∘ assocˡ

  inAssocˡ′ : (a × b ⇨ a′ × b′) → (a × (b × c) ⇨ a′ × (b′ × c))
  inAssocˡ′ = inAssocˡ ∘′ first

  inAssocʳ : (a × (b × c) ⇨ a′ × (b′ × c′)) → ((a × b) × c ⇨ (a′ × b′) × c′)
  inAssocʳ f = assocˡ ∘ f ∘ assocʳ

  inAssocʳ′ : (b × c ⇨ b′ × c′) → ((a × b) × c ⇨ (a × b′) × c′)
  inAssocʳ′ = inAssocʳ ∘′ second

  swap : a × b ⇨ b × a
  swap = exr ▵ exl

  transpose : (a × b) × (c × d) ⇨ (a × c) × (b × d)
  transpose = inAssocʳ′ (inAssocˡ′ swap)

  infixr 4 _⦂_
  -- _⦂_ : ⌞ a ⌟ → ⌞ b ⌟ → ⌞ a × b ⌟
  _⦂_ : (⊤ ⇨ a) → (⊤ ⇨ b) → (⊤ ⇨ a × b)
  a ⦂ b = (a ⊗ b) ∘ unitorⁱˡ


open Cartesian ⦃ … ⦄ public

record CartesianClosed {obj : Set o}
         ⦃ _ : Products obj ⦄ ⦃ _ : Exponentials obj ⦄
         (_⇨′_ : obj → obj → Set ℓ) : Set (o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    ⦃ ⇨Cartesian ⦄ : Cartesian _⇨_
    curry : (a × b ⇨ c) → (a ⇨ (b ⇛ c))
    apply : (a ⇛ b) × a ⇨ b

  uncurry : (a ⇨ (b ⇛ c)) → (a × b ⇨ c)
  uncurry f = apply ∘ first f

open CartesianClosed ⦃ … ⦄ public


record Logic {obj : Set o} ⦃ products : Products obj ⦄ ⦃ boolean : Boolean obj ⦄
             (_⇨′_ : obj → obj → Set ℓ) : Set (o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    false true : ⊤ ⇨ Bool
    not : Bool ⇨ Bool
    ∧ ∨ xor : Bool × Bool ⇨ Bool
    cond : Bool × (a × a) ⇨ a

open Logic ⦃ … ⦄ public
