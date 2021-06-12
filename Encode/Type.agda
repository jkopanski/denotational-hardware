{-# OPTIONS --safe --without-K #-}

-- Change-of-representation functor. Some implementations restrict the shapes of
-- data, thus requiring decoding from a restricted representation into a more
-- natural type. For instance, a digital circuit manipulates bit vectors that
-- representing a variety of types.

-- For instance, circuits map between bit vector streams so their objects are
-- natural numbers, and a circuit is some `h : m ↠ n` for `m n : ℕ`. The meaning
-- (homomorphic image) of `h` is some `f′ : Vec Bool m → Vec Bool n`. A more
-- natural expression of `f′` may be a function `f : u → v`, where `Vec Bool m`
-- and `Vec Bool n` are encodings of more natural types `u` and `v`.

-- TODO: How does this functor relate to the worker-wrapper transformation?

-- TODO: Are we defining an adjunction? If not, should it be; and if so, is it a
-- common adjunction?

open import Level

open import Categorical.Raw
open import Categorical.Equiv

module Encode.Type {o} {obj : Set o}
                   {ℓ} (_↠_ : obj → obj → Set ℓ) ⦃ _ : Category _↠_ ⦄
                   q ⦃ _ : Equivalent q _↠_ ⦄
                   {o′} {obj′ : Set o′} (⟦_⟧ : obj′ → obj)
 where

-- TODO: Is this version the categorical dual of Decode? Or maybe it's the dual
-- of the decoder for the dual of the underlying category. In other words, the
-- dual an encoder is the decoder of the dual.

-- Encoder
record D : Set (o ⊔ o′ ⊔ ℓ) where
  constructor mk
  field
    { τ  } : obj     -- meaning
    { τ′ } : obj′    -- representation
    e : τ ↠ ⟦ τ′ ⟧   -- interpret representation ("encode")

infix 0 _⇨_
record _⇨_ (a : D) (b : D) : Set (q ⊔ ℓ) where
  constructor mk
  open D
  field
    f  : τ  a ↠ τ  b
    f′ : ⟦ τ′ a ⟧ ↠ ⟦ τ′ b ⟧
    spec : e b ∘ f ≈ f′ ∘ e a

module decode-type-instances where

  open import Categorical.Equiv
  open D ; open _⇨_

  instance
  
    -- Forgetful functor from _⇨_ to _↠_

    homomorphismₒ : Homomorphismₒ D obj
    homomorphismₒ = record { Fₒ = τ }

    homomorphism : Homomorphism _⇨_ _↠_
    homomorphism = record { Fₘ = _⇨_.f }
