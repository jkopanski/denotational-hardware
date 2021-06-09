{-# OPTIONS --safe --without-K #-}

-- Change-of-representation functor. Some implementations restrict the shapes of
-- data, thus requiring decoding from a restricted representation into a more
-- natural type.

open import Level

open import Categorical.Raw
open import Categorical.Equiv

module Decode.Type {o} {obj : Set o}
                   {ℓ} (_↠_ : obj → obj → Set ℓ) ⦃ _ : Category _↠_ ⦄
                   q ⦃ _ : Equivalent q _↠_ ⦄
                   {o′} {obj′ : Set o′} (⟦_⟧ : obj′ → obj)
 where

-- Decoder
record D : Set (o ⊔ o′ ⊔ ℓ) where
  constructor mk
  field
    { τ  } : obj     -- meaning
    { τ′ } : obj′    -- representation
    d : ⟦ τ′ ⟧ ↠ τ   -- interpret representation ("decode")

infix 0 _⇨_
record _⇨_ (a : D) (b : D) : Set (q ⊔ ℓ) where
  constructor mk
  open D
  field
    f  : τ  a ↠ τ  b
    f′ : ⟦ τ′ a ⟧ ↠ ⟦ τ′ b ⟧
    spec : d b ∘ f′ ≈ f ∘ d a

module decode-type-instances where

  open import Categorical.Equiv
  open D ; open _⇨_

  instance
  
    -- Forgetful functor from _⇨_ to _↠_

    homomorphismₛₒ : Homomorphismₒ D obj
    homomorphismₛₒ = record { Fₒ = τ }

    homomorphismₛ : Homomorphism _⇨_ _↠_
    homomorphismₛ = record { Fₘ = _⇨_.f }
