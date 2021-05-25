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


open import Categorical.Object
open import Categorical.Equiv

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


open import Data.Nat

-- Cardinality of a type
card : Ty → ℕ
card `⊤ = 1
card `Bool = 2
card (a `× b) = card a * card b
card (a `⇛ b) = card b ^ card a

{-
open import Level using (0ℓ)
open import Data.Fin as F hiding (_+_)
open import Functions.Type 0ℓ
open import Data.Product using (_,_)

-- Defined somewhere?
mulFin : ∀ {m n} → Fin m → Fin n → Fin (n * m)
mulFin i  zero   = inject+ _ i
mulFin i (suc j) = raise _ (mulFin i j)

toFin : ∀ a → Fₒ a → Fin (card a)
toFin `⊤ tt = zero
toFin `Bool 𝕗 = zero
toFin `Bool 𝕥 = suc zero
toFin (a `× b) (x , y) = mulFin (toFin b y) (toFin a x)
toFin (a `⇛ b) f = {!!}

-- TODO: Define an isomorphism, including proofs.

-}

-- # of bits in a value of a given type (maybe rename to "#bits").
-- Log₂ of cardinality.
size : Ty → ℕ
size `⊤       = 0
size `Bool    = 1
size (a `× b) = size a + size b
size (a `⇛ b) = size b * card a

-- See Ty.Properties for proof of ∀ a → card a ≡ 2 ^ size a

{-

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
