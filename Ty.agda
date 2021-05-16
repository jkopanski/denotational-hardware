-- Simple type/object encodings

module Ty where

open import Data.Nat

infixr 2 _`×_
infixr 0 _`⇛_
data Ty : Set where
  `⊤    : Ty
  `Bool : Ty
  _`×_  : Ty → Ty → Ty
  _`⇛_  : Ty → Ty → Ty


module ty-instances where

  open import Categorical.Equiv
  open import Categorical.Raw
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
       h `⊤ = ⊤
       h `Bool = Bool
       h (a `× b) = h a × h b
       h (a `⇛ b) = h a ⇛ h b
