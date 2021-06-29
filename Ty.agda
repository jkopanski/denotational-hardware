{-# OPTIONS --safe --without-K #-}
-- Simple type/object encodings

module Ty where

infixr 2 _`×_
infixr 0 _`⇛_
data Ty : Set where
  `⊤    : Ty
  `Bool : Ty
  _`×_  : Ty → Ty → Ty
  _`⇛_  : Ty → Ty → Ty

open import Categorical.Homomorphism
import Categorical.Laws as L

module ty-instances where

  instance

    products : Products Ty
    products = record { ⊤ = `⊤ ; _×_ = _`×_ }

    exponentials : Exponentials Ty
    exponentials = record { _⇛_ = _`⇛_ }

    boolean : Boolean Ty
    boolean = record { Bool = `Bool }

    homomorphismₒ : ∀ {o}{obj : Set o}
        ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄ ⦃ _ : Exponentials obj ⦄
      → Homomorphismₒ Ty obj
    homomorphismₒ {obj = obj} = record { Fₒ = h }
      where
        h : Ty → obj
        h   `⊤     = ⊤
        h  `Bool   = Bool
        h (a `× b) = h a × h b
        h (a `⇛ b) = h a ⇛ h b

    productsH : ∀ {ℓ o}{obj : Set o} ⦃ _ : Products obj ⦄
                  ⦃ _ : Boolean obj ⦄ ⦃ _ : Exponentials obj ⦄
                  {_⇨_ : obj → obj → Set ℓ} ⦃ _ : Category _⇨_ ⦄
                  {q} ⦃ _ : Equivalent q _⇨_ ⦄ ⦃ _ : L.Category _⇨_ ⦄
             → ProductsH Ty _⇨_
    productsH = record
      { ε = id ; μ = id ; ε⁻¹ = id ; μ⁻¹ = id
      ; ε⁻¹∘ε = L.identityˡ ; ε∘ε⁻¹ = L.identityˡ
      ; μ⁻¹∘μ = L.identityˡ ; μ∘μ⁻¹ = L.identityˡ
      }

    exponentialsH : ∀ {ℓ o}{obj : Set o} ⦃ _ : Products obj ⦄
                    ⦃ _ : Boolean obj ⦄ ⦃ _ : Exponentials obj ⦄
                    {_⇨_ : obj → obj → Set ℓ} ⦃ _ : Category _⇨_ ⦄
             → ExponentialsH Ty _⇨_
    exponentialsH = record { ν = id ; ν⁻¹ = id }

    booleanH : ∀ {ℓ o}{obj : Set o} ⦃ _ : Products obj ⦄
               ⦃ _ : Boolean obj ⦄ ⦃ _ : Exponentials obj ⦄
               {_⇨_ : obj → obj → Set ℓ} ⦃ _ : Category _⇨_ ⦄
             → BooleanH Ty _⇨_
    booleanH = record { β = id ; β⁻¹ = id }


open import Data.Nat

-- # of atomic values (bits or functions) in each value of a given type
#atoms : Ty → ℕ
#atoms `⊤       = 0
#atoms `Bool    = 1
#atoms (a `× b) = #atoms a + #atoms b
#atoms (a `⇛ b) = 1

{-

-- Ty-indexed equivalence relation. Currently unused.

module _ where

  open import Level
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality hiding (refl)
  open import Data.Bool
  open import Data.Product using (_,_)

  open import Functions.Type

  eqₜ : ∀ (a : Ty) → Rel (Fₒ a) 0ℓ
  eqₜ `⊤ tt tt = ⊤
  eqₜ `Bool  b₁ b₂ = b₁ ≡ b₂
  eqₜ (a `× b) (u₁ , u₂) (v₁ , v₂) = eqₜ a u₁ v₁ × eqₜ b u₂ v₂
  eqₜ (a `⇛ b) f g = -- ∀ {x y : Fₒ a} → eqₜ a x y → eqₜ b (f x) (g y)
                    ∀ {x : Fₒ a} → eqₜ b (f x) (g x)

  -- I think the explicit Ty arguments are needed due to lack of Fₒ injectivity
  -- See if the following infix version is useful elsewhere.

  -- infix 4 _≡ₜ_
  -- _≡ₜ_ : ∀ {a : Ty} → Rel (Fₒ a) 0ℓ
  -- _≡ₜ_ {a} = eqₜ a

  open import Data.Unit
  -- import Relation.Binary.PropositionalEquality.Properties as ≡
  open import Data.Product.Relation.Binary.Pointwise.NonDependent

  isEquivₜ : ∀ {a} → IsEquivalence (eqₜ a)
  isEquivₜ {  `⊤  } = _
  isEquivₜ {`Bool } = isEquivalence
  isEquivₜ {a `× b} = ×-isEquivalence isEquivₜ isEquivₜ
  isEquivₜ {a `⇛ b} = record
    { refl  = b.refl
    ; sym   = λ f≈g → b.sym f≈g
    ; trans = λ f≈g g≈h → b.trans f≈g g≈h
    }
   where module b = IsEquivalence (isEquivₜ {b})

-}
