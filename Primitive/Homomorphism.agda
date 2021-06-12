{-# OPTIONS --safe --without-K #-}

open import Level

open import Categorical.Raw
open import Categorical.Equiv
open import Categorical.Homomorphism
open import Categorical.Laws as L hiding (Cartesian)
open import Ty


module Primitive.Homomorphism
    {o ℓ} {obj : Set o}
    ⦃ _ : Products obj ⦄ ⦃ _ : Exponentials obj ⦄ ⦃ _ : Boolean obj ⦄
    (_↠_ : obj → obj → Set ℓ) (let infix 0 _↠_; _↠_ = _↠_)
    ⦃ _ : Logic _↠_ ⦄
    {q : Level} ⦃ _ : Equivalent q _↠_ ⦄
    -- For logicH:
    ⦃ _ : Cartesian _↠_ ⦄ ⦃ _ : L.Cartesian _↠_ q ⦄
 where

open import Primitive.Raw _↠_ public

private variable a b c : obj

-- TODO: fill in (https://github.com/conal/agda-hardware/issues/6)

instance

  import Categorical.Raw as C
  open ≈-Reasoning
  open import Relation.Binary.PropositionalEquality hiding (sym; refl)

  logicH : LogicH _⇨_ _↠_ q
  logicH = record
    { F-false = Fₘ-f∘ε≈β∘f false
    ; F-true  = Fₘ-f∘ε≈β∘f true
    ; F-not =
        begin
          Fₘ not ∘ β
        ≡⟨⟩
          not ∘ id
        ≈⟨ identityʳ ⟩
          not
        ≈˘⟨ identityˡ ⟩
          id ∘ not
        ≡⟨⟩
          β ∘ not
        ∎
    ; F-∧ = Fₘ-f∘μ∘β⊗β≈β∘f ∧
    ; F-∨ = Fₘ-f∘μ∘β⊗β≈β∘f ∨
    ; F-xor = Fₘ-f∘μ∘β⊗β≈β∘f xor
    ; F-cond = λ {a} →
        begin
            Fₘ (cond {a = a}) ∘ μ {a = Bool} {b = a × a} ∘ (β ⊗ μ {a = a} {b = a} )
        ≡⟨⟩
          cond ∘ id ∘ (id ⊗ id)
        ≈⟨ ∘≈ʳ identityˡ ⟩
          cond ∘ (id ⊗ id)
        ≈⟨ ∘≈ʳ id⊗id ⟩
          cond ∘ id
        ≈⟨ identityʳ ⟩
            cond
        ∎
    }
    where
      Fₘ-f∘ε≈β∘f : (f : ⊤ ⇨ Bool) {f′ : ⊤ ↠ Bool} →  ⦃ Fₘ f ≡ f′ ⦄ → Fₘ f ∘ ε ≈ β ∘ f′
      Fₘ-f∘ε≈β∘f f {f′} ⦃ _≡_.refl ⦄ =
        begin
          Fₘ f ∘ ε
        ≡⟨⟩
          f′ ∘ ε
        ≈⟨ identityʳ ⟩
          f′
        ≈˘⟨ identityˡ ⟩
          id ∘ f′
        ≡⟨⟩
          β ∘ f′
        ∎
      Fₘ-f∘μ∘β⊗β≈β∘f : (f : Bool × Bool ⇨ Bool) {f′ : Bool × Bool ↠ Bool} → ⦃ Fₘ f ≡ f′ ⦄
                     → Fₘ f ∘ μ {a = Bool} {b = Bool} ∘ (β ⊗ β) ≈ β ∘ f′
      Fₘ-f∘μ∘β⊗β≈β∘f f {f′} ⦃ _≡_.refl ⦄ =
        begin
          Fₘ f ∘ μ {a = Bool} {b = Bool} ∘ (β ⊗ β)
        ≡⟨⟩
          f′ ∘ id ∘ (id ⊗ id)
        ≈⟨ ∘≈ʳ identityˡ ⟩
          f′ ∘ (id ⊗ id)
        ≈⟨ ∘≈ʳ id⊗id ⟩
          f′ ∘ id
        ≈⟨ identityʳ ⟩
          f′
        ≈˘⟨ identityˡ ⟩
          id ∘ f′
        ≡⟨⟩
          β ∘ f′
        ∎
