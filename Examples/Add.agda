{-# OPTIONS --safe --without-K #-}

open import Level using (0ℓ)
open import Data.Nat

open import Categorical.Raw
open import Functions.Raw

module Examples.Add
         {o} {obj : Set o} ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄
         {_⇨_ : obj → obj → Set} (let private infix 0 _⇨_; _⇨_ = _⇨_)
         ⦃ _ : Cartesian _⇨_ ⦄ ⦃ _ : Logic _⇨_ ⦄
 where

-- TODO: package up module parameters into one record to pass in and open.

private variable a b c : obj

-- Morphism with carry-in and carry-out
infix 0 _⇨ᶜ_
_⇨ᶜ_ : obj → obj → Set
a ⇨ᶜ b = Bool × a ⇨ b × Bool

-- Summands ⇨ sum , carry
-- λ (a , b) → (a ⊕ b , a ∧ b)
halfAdd : Bool ⇨ᶜ Bool
halfAdd = xor ▵ ∧

fullAdd : Bool × Bool ⇨ᶜ Bool
fullAdd = second ∨ ∘ inAssocˡ′ halfAdd ∘ second halfAdd

-- λ (c , (a , b)) → let (p , d) = halfAdd (a , b)
--                       (q , e) = halfAdd (c , p) in (q , e ∨ d)

-- c , (a , b)
-- c , (p , d)
-- q , (e , d)
-- q , e ∨ d

-- TODO: semantic specifications and correctness proofs.

ripple : (a ⇨ᶜ b) → (n : ℕ) → (V a n ⇨ᶜ V b n)
ripple f  zero   = swap
ripple f (suc n) = assocˡ ∘ second (ripple f n) ∘ inAssocˡ′ f

-- cᵢ , (a , as)
-- b , (c′ , as)
-- b , (bs , cₒ)
-- (b , bs) , cₒ

rippleAdd : ∀ n → V (Bool × Bool) n ⇨ᶜ V Bool n
rippleAdd = ripple fullAdd

constˡ : (a × b ⇨ c) → (⊤ ⇨ a) → (b ⇨ c)
constˡ f a = f ∘ first a ∘ unitorⁱˡ

-- b
-- tt , b
-- a , b
-- f (a , b)

speculate : (Bool × a ⇨ b) → (Bool × a ⇨ b)
speculate f = cond ∘ second (constˡ f false ▵ constˡ f true)

-- (cᵢ , a)
-- (cᵢ , (f (false , a) , f (true , a)))
-- cond (cᵢ , (f (false , a) , f (true , a)))

V² : obj → ℕ → ℕ → obj
V² a m n = V (V a n) m

carrySelect : ∀ m n → V² (Bool × Bool) m n ⇨ᶜ V² Bool m n
carrySelect m n = ripple (speculate (ripple fullAdd n)) m
