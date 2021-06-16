-- 1D convolution from "Type-Directed Scheduling of Streaming Accelerators"

module Examples.Conv where

open import Data.Product hiding (map; zip)
open import Function
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Vec

private
  variable
    m n : ℕ
    a b s : Set

-- Note: I think the definitions would simpler 

shiftʳ : a → Vec a n → Vec a n
shiftʳ x₀ [] = []
shiftʳ x₀ (x ∷ xs) = x₀ ∷ shiftʳ x xs

avg : ℕ × ℕ × ℕ → ℕ
avg (p , q , r) = (p + q + r) div 3

ℕ² : Set
ℕ² = ℕ × ℕ

conv : ℕ² × Vec ℕ m → Vec ℕ m
conv ((a , b) , v₂) = map avg (zip v₀ (zip v₁ v₂))
 where
   v₁ = shiftʳ b v₂
   v₀ = shiftʳ a v₁

mealy : (s × a → b × s) → (∀ {n} → s × Vec a n → Vec b n)
mealy f (s , []) = []
mealy f (s , x ∷ xs) = let b , s′ = f (s , x) in b ∷ mealy f (s′ , xs)

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Now write conv via mealy.

-- Figure 1a in "Type-Directed Scheduling of Streaming Accelerators"

conv₁ : ℕ² × Vec ℕ m → Vec ℕ m
conv₁ = mealy λ ((a , b) , c) → avg (a , b , c) , (b , c)

conv₁-spec : conv₁ ≗ conv {m}
conv₁-spec (_ , []) = refl
conv₁-spec ((_ , q) , x ∷ xs) rewrite conv₁-spec ((q , x) , xs) = refl

-- Figure 1b

conv₂ : ℕ² × Vec ℕ² m → Vec ℕ² m
conv₂ = mealy λ ((a , b) , (c , d)) →
          (avg (a , b , c) , avg (b , c , d)) , (c , d)

-- Note: we could drop from four adders to three by removing a redundant b + c.
-- I think one addition and one subtraction suffices for any window width.

decode₂ : Vec ℕ² m → Vec ℕ (m * 2)
decode₂ [] = []
decode₂ ((x , y) ∷ xys) = x ∷ y ∷ decode₂ xys

conv₂-spec : decode₂ ∘ conv₂ {m} ≗ conv {m * 2} ∘ map₂ decode₂
conv₂-spec {zero } (_ ,   []  ) = refl
conv₂-spec {suc _} (_ , p ∷ ps) rewrite conv₂-spec (p , ps) = refl
