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

shift′ : a × Vec a n → Vec a n × a
shift′ (x₀ , []) = ([] , x₀)
shift′ (x₀ , x ∷ xs) = map₁ (x₀ ∷_) (shift′ (x , xs))

shift : a → Vec a n → Vec a n
-- shift x xs = proj₁ (shift′ (x , xs))

shift = curry (proj₁ ∘ shift′)

-- shift a₀ as = take _ (a₀ ∷ as)

avg : ℕ × ℕ × ℕ → ℕ
avg (p , q , r) = (p + q + r) div 3

conv : Vec ℕ m → Vec ℕ m
conv v₀ = map avg (zip v₀ (zip v₁ v₂))
 where
   v₁ = shift 0 v₀
   v₂ = shift 0 v₁

-- conv v₀ = let v₁ = shift 0 v₀ ; v₂ = shift 0 v₁ in map avg (zip v₀ (zip v₁ v₂))

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

conv′ : (ℕ × ℕ) × Vec ℕ m → Vec ℕ m × (ℕ × ℕ)
conv′ ((p , q) , v₀) =
  let (v₁ , z) = shift′ (q , v₀)
      (v₂ , y) = shift′ (p , v₁)
  in
    map avg (zip v₀ (zip v₁ v₂)) , (y , z)


conv≡conv′ : ∀ {n} {v : Vec ℕ n} → conv v ≡ proj₁ (conv′ ((0 , 0) , v))
conv≡conv′ = refl

mealy : (s × a → b × s) → (∀ {n} → s × Vec a n → Vec b n × s)
mealy f (s , []) = [] , s
mealy f (s , a ∷ as) = let b , s′ = f (s , a) in map₁ (b ∷_) (mealy f (s′ , as))

-- TODO: Write conv via mealy

h₁ : (ℕ × ℕ) × ℕ → ℕ × (ℕ × ℕ)
h₁ ((a , b) , c) = avg (a , b , c) , (b , c)

conv₁ : (ℕ × ℕ) → Vec ℕ m → Vec ℕ m
-- conv₁ pq v₀ = proj₁ (mealy h₁ (pq , v₀))

conv₁ = curry (proj₁ ∘ mealy h₁)

{-

conv₁≗conv : ∀ {m} pq → conv₁ pq ≗ conv {m} pq
conv₁≗conv (p , q) [] = refl
conv₁≗conv (p , q) (a ∷ as) =
    begin
      conv₁ (p , q) (a ∷ as)
    ≡⟨⟩
      proj₁ (mealy h₁ ((p , q) , a ∷ as))
    ≡⟨⟩
      proj₁ (let b , (p′ , q′) = h₁ ((p , q) , a) in
              map₁ (b ∷_) (mealy h₁ ((p′ , q′) , as)))

    ≡⟨⟩
      proj₁ (map₁ (avg (p , q , a) ∷_) (mealy h₁ ((q , a) , as)))

    ≡⟨ {!!} ⟩
      {!!}
    ≡⟨⟩
      conv (p , q) (a ∷ as)
    ∎

-- I think we'll have to generalize.

-- We can simplify away the averaging, and add it from the outside.

-}
