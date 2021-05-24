{-# OPTIONS --safe --without-K #-}

module Fun.Type where

open import Categorical.Object

open import Functions.Type
open import Ty

⟦_⟧ : Ty → Set
⟦   `⊤   ⟧ = ⊤
⟦ `Bool  ⟧ = Bool
⟦ a `× b ⟧ = ⟦ a ⟧ × ⟦ b ⟧
⟦ a `⇛ b ⟧ = ⟦ a ⟧ → ⟦ b ⟧

infix 0 _⇨_
record _⇨_ (a b : Ty) : Set where
  constructor mk
  field
    f : ⟦ a ⟧ → ⟦ b ⟧  -- or ⟦ a ⇛ b ⟧


module fun-instances where

  open import Categorical.Object

  instance

    products : Products Ty
    products = record { ⊤ = `⊤ ; _×_ = _`×_ }

    exponentials : Exponentials Ty
    exponentials = record { _⇛_ = _`⇛_ }

    boolean : Boolean Ty
    boolean = record { Bool = `Bool }
