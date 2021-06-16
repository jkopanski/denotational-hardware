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

shift : a × Vec a n → Vec a n × a
shift (x₀ , []) = ([] , x₀)
shift (x₀ , x ∷ xs) = map₁ (x₀ ∷_) (shift (x , xs))

avg : ℕ × ℕ × ℕ → ℕ
avg (p , q , r) = (p + q + r) div 3

conv : (ℕ × ℕ) × Vec ℕ m → Vec ℕ m × (ℕ × ℕ)
conv ((p , q) , v₂) =
  let (v₁ , z) = shift (q , v₂)
      (v₀ , y) = shift (p , v₁)
  in
    map avg (zip v₀ (zip v₁ v₂)) , (y , z)

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

mealy : (s × a → b × s) → (∀ {n} → s × Vec a n → Vec b n × s)
mealy f (s , []) = [] , s
mealy f (s , x ∷ xs) = let b , s′ = f (s , x) in map₁ (b ∷_) (mealy f (s′ , xs))

-- Now write conv via mealy

h₁ : (ℕ × ℕ) × ℕ → ℕ × (ℕ × ℕ)
h₁ ((a , b) , c) = avg (a , b , c) , (b , c)

conv₁ : (ℕ × ℕ) × Vec ℕ m → Vec ℕ m × (ℕ × ℕ)
conv₁ = mealy h₁

conv₁≗conv : ∀ {m} → conv₁ ≗ conv {m}
conv₁≗conv ((p , q) , []) = refl
conv₁≗conv ((p , q) , x ∷ xs) rewrite conv₁≗conv ((q , x) , xs) = refl
