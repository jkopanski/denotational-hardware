{-# OPTIONS --safe --without-K #-}
-- Miscellaneous utilities, perhaps to move elsewhere

open import Categorical.Raw
open import Ty

module Ty.Utils {ℓ}
  {_⇨_ : Ty → Ty → Set ℓ} (let infix 0 _⇨_; _⇨_ = _⇨_)
  ⦃ _ : Cartesian _⇨_ ⦄
  where

open import Data.Nat

private variable a : Ty

-- Todo: rename
replicate′ : ∀ n → (⊤ ⇨ a) → (⊤ ⇨ V a n)
replicate′ zero    a = !
replicate′ (suc n) a = a ⦂ replicate′ n a

shiftR : Bool × a ⇨ a × Bool
shiftR {`⊤}     = swap
shiftR {`Bool}  = swap
shiftR {_ `× _} = assocˡ ∘ second shiftR ∘ assocʳ ∘ first shiftR ∘ assocˡ
shiftR {_ `⇛ _} = swap

-- i , (u , v)
-- (i , u) , v
-- (u′ , m) , v
-- u′ , (m , v)
-- u′ , (v′ , o)
-- (u′ , v′) , o

shiftL : a × Bool ⇨ Bool × a
shiftL {`⊤}     = swap
shiftL {`Bool } = swap
shiftL {_ `× _} = assocʳ ∘ first shiftL ∘ assocˡ ∘ second shiftL ∘ assocʳ
shiftL {_ `⇛ _} = swap

-- (u , v) , i
-- u , (v , i)
-- u , (m , v′)
-- (u , m) , v′
-- (o , u′) , v′
-- o , (u′ , v′)

shiftR⇃ : Bool × a ⇨ a
shiftR⇃ = exl ∘ shiftR

shiftL⇃ : a × Bool ⇨ a
shiftL⇃ = exr ∘ shiftL
