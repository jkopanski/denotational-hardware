module SetFinite where

-- Full subcategory of Function restricted to finite sets.

-- TODO: Try generalizing from functions to any category with sets as objects.

open import Level using (0ℓ)
open import Function using (_↔_; mk↔′; Inverse)
open import Data.Product using (Σ; _,_)
open import Data.Nat
open import Data.Fin renaming (Fin to 𝔽)
open import Data.Fin.Properties
open import Data.Fin.Patterns using (0F; 1F)
open import Relation.Binary.PropositionalEquality using (refl)

open import Categorical.Homomorphism hiding (refl)
open import Categorical.Laws
open import Functions 0ℓ
import Finite.Object

-- A finite set, demonstrated by a number n and proof that A ≅ 𝔽 n.
record SetFinite : Set₁ where
  constructor mk
  field
    { A } : Set
    { n } : ℕ
    iso : A ↔ 𝔽 n

module set-finite-instances where

  instance

    Hₒ : Homomorphismₒ SetFinite Set
    Hₒ = record { Fₒ = SetFinite.A }

    open import Categorical.Reasoning

    products : Products SetFinite
    products = record
      { ⊤ = mk (mk↔′ ε ε⁻¹ ε∘ε⁻¹ ε⁻¹∘ε)
      ; _×_ = λ (mk {A} {m} record {f = f; f⁻¹ = f⁻¹; inverse = f∘f⁻¹ , f⁻¹∘f})
                (mk {B} {n} record {f = g; f⁻¹ = g⁻¹; inverse = g∘g⁻¹ , g⁻¹∘g}) →
                let open ≈-Reasoning in
         mk {A × B} {m × n}
           (mk↔′ (μ ∘ (f ⊗ g)) ((f⁻¹ ⊗ g⁻¹) ∘ μ⁻¹)
             (begin
                (μ ∘ (f ⊗ g)) ∘ ((f⁻¹ ⊗ g⁻¹) ∘ μ⁻¹)
              ≈⟨ cancelInner
                   {i = f⁻¹ ⊗ g⁻¹} {h = f ⊗ g}
                   (⊗-inverse {f = f⁻¹} {f} {g⁻¹} {g} f∘f⁻¹ g∘g⁻¹)
                   {f = μ} {g = μ⁻¹} ⟩
                 μ ∘ μ⁻¹ {a = m}
              ≈⟨ μ∘μ⁻¹ {a = m} ⟩
                id
              ∎)
             (begin
                ((f⁻¹ ⊗ g⁻¹) ∘ μ⁻¹) ∘ (μ ∘ (f ⊗ g))
              ≈⟨ cancelInner {i = μ} {h = μ⁻¹} μ⁻¹∘μ {f = f⁻¹ ⊗ g⁻¹} {g = f ⊗ g} ⟩
                 (f⁻¹ ⊗ g⁻¹) ∘ (f ⊗ g)
              ≈⟨ (⊗-inverse {f = f} {f⁻¹} {g} {g⁻¹} f⁻¹∘f g⁻¹∘g) ⟩
                id
              ∎)
           )
      }

    productsH : ProductsH SetFinite ⟨→⟩
    productsH = record
                  { ε     = id
                  ; μ     = id
                  ; ε⁻¹   = id
                  ; μ⁻¹   = id
                  ; ε⁻¹∘ε = λ _ → refl
                  ; ε∘ε⁻¹ = λ _ → refl
                  ; μ⁻¹∘μ = λ _ → refl
                  ; μ∘μ⁻¹ = λ _ → refl
                  }

    -- TODO: Coproducts
    -- TODO: Exponentials

    boolean : Boolean SetFinite
    boolean = record { Bool = mk (mk↔′ β β⁻¹ β∘β⁻¹ β⁻¹∘β) }

    booleanH : BooleanH SetFinite ⟨→⟩
    booleanH = record { β = id ; β⁻¹ = id }

    strongBooleanH : StrongBooleanH SetFinite ⟨→⟩
    strongBooleanH = record { β⁻¹∘β = λ _ → refl ; β∘β⁻¹ = λ _ → refl }

-- Define the subcategory of ⟨→⟩ with homomorphisms and laws
open import Categorical.Subcategory ⟨→⟩ SetFinite public
