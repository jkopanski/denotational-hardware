{-# OPTIONS --safe --without-K #-}

module Fun.Type where

open import Data.Unit
open import Data.Product
open import Data.Bool

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


module →-instances where

  open import Categorical.Object

  instance

    products : Products Ty
    products = record { ⊤ = `⊤ ; _×_ = _`×_ }

    exponentials : Exponentials Ty
    exponentials = record { _⇛_ = _`⇛_ }

    boolean : Boolean Ty
    boolean = record { Bool = `Bool }
