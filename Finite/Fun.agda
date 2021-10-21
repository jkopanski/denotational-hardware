{-# OPTIONS --safe --without-K #-}

-- This functionality is also in https://github.com/agda/agda-stdlib/pull/1613

module Finite.Fun where

open import Function using (case_of_)
open import Data.Nat
open import Data.Fin renaming (Fin to 𝔽)
open import Data.Fin.Properties
open import Function using (id; _∘_)
open import Data.Product


fun→fin : ∀ {m n} → (𝔽 m → 𝔽 n) → 𝔽 (n ^ m)
fun→fin {zero } f = zero
fun→fin {suc m} f = combine (f zero) (fun→fin (f ∘ suc))

fin→fun : ∀ {m n} → 𝔽 (n ^ m) → (𝔽 m → 𝔽 n)
fin→fun {suc m} {n} k  zero   = proj₁ (remQuot {n} (n ^ m) k)
fin→fun {suc m} {n} k (suc i) = fin→fun {m} (proj₂ (remQuot {n} (n ^ m) k)) i

-- fin→fun : ∀ {m n} → 𝔽 (n ^ m) → (𝔽 m → 𝔽 n)
-- fin→fun {suc m} {n} k i with remQuot {n} (n ^ m) k
-- fin→fun {suc m} _  zero   | j ,  _  = j
-- fin→fun {suc m} _ (suc i) | _ , n^m = fin→fun n^m i

-- fin→fun : ∀ {m n} → 𝔽 (n ^ m) → (𝔽 m → 𝔽 n)
-- fin→fun {suc m} {n} k i = case i , remQuot {n} (n ^ m) k of λ
--   { ( zero , j ,  _ )  → j
--   ; (suc i , _ , n^m) → fin→fun n^m i }

open import Relation.Binary.PropositionalEquality; open ≡-Reasoning

fin→fun→fin : ∀ {m n} → fun→fin {m}{n} ∘ fin→fun ≗ id
fin→fun→fin {zero}  {n} zero = refl
fin→fun→fin {suc m} {n} k =
  begin
    combine (fin→fun {suc m}{n} k zero) (fun→fin (λ i → fin→fun {suc m}{n} k (suc i)))
  ≡⟨⟩
    combine (proj₁ (remQuot {n} (n ^ m) k))
      (fun→fin (fin→fun {m} (proj₂ (remQuot {n} (n ^ m) k))))
  ≡⟨ cong (λ □ → combine (proj₁ (remQuot {n} (n ^ m) k)) □)
       (fin→fun→fin {m} (proj₂ (remQuot {n} (n ^ m) k))) ⟩
    combine (proj₁ (remQuot {n} (n ^ m) k)) (proj₂ (remQuot {n} (n ^ m) k))
  ≡⟨⟩
    uncurry combine (remQuot {n} (n ^ m) k)
  ≡⟨ combine-remQuot {n = n} (n ^ m) k ⟩
    k
  ∎

fun→fin→fun : ∀ {m n} (f : 𝔽 m → 𝔽 n) → fin→fun (fun→fin f) ≗ f
fun→fin→fun {suc m} {n} f  zero   =
  begin
    proj₁ (remQuot (n ^ m) (combine (f zero) (fun→fin (f ∘ suc))))
  ≡⟨ cong proj₁ (remQuot-combine _ _) ⟩
    proj₁ (f zero , fun→fin (f ∘ suc))
  ≡⟨⟩
    f zero
  ∎
fun→fin→fun {suc m} {n} f (suc i) =
  begin
    fin→fun (proj₂ (remQuot {n} (n ^ m) (combine (f zero) (fun→fin (f ∘ suc))))) i
  ≡⟨ cong (λ □ → fin→fun (proj₂ □) i) (remQuot-combine {n} _ _) ⟩
    fin→fun (proj₂ (f zero , fun→fin (f ∘ suc))) i
  ≡⟨⟩
    fin→fun (fun→fin (f ∘ suc)) i
  ≡⟨ fun→fin→fun (f ∘ suc) i ⟩
    (f ∘ suc) i
  ≡⟨⟩
    f (suc i)
  ∎
