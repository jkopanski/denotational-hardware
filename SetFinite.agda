module SetFinite where

-- Full subcategory of Function restricted to finite sets. Finiteness of a type
-- A is demonstrated by a number n and proof that 𝔽 n ≅ A.

open import Level using (0ℓ)
open import Function using (_↔_; mk↔′; Inverse)
open import Data.Product using (Σ; _,_) renaming (_×_ to _×′_)
open import Data.Nat
open import Data.Fin renaming (Fin to 𝔽)
open import Data.Fin.Properties
open import Data.Fin.Patterns
open import Relation.Binary.PropositionalEquality using () renaming (refl to refl≡)

open import Categorical.Homomorphism hiding (refl)
open import Categorical.Laws
open import Functions 0ℓ
import Finite.Object

record SetFinite : Set₁ where
  constructor mk
  field
    { A } : Set
    { n } : ℕ
    iso : 𝔽 n ↔ A


module set-finite-instances where

  instance

    Hₒ : Homomorphismₒ SetFinite Set
    Hₒ = record { Fₒ = SetFinite.A }

    open import Categorical.Reasoning

    products : Products SetFinite
    products = record
      { ⊤ = mk 1↔⊤
      ; _×_ = λ (mk {A} {m} record {f = f; f⁻¹ = f⁻¹; inverse = f∘f⁻¹ , f⁻¹∘f})
                (mk {B} {n} record {f = g; f⁻¹ = g⁻¹; inverse = g∘g⁻¹ , g⁻¹∘g}) →
         mk {A × B} {m × n}
           (mk↔′ ((f ⊗ g) ∘ μ⁻¹) (μ ∘ (f⁻¹ ⊗ g⁻¹))
                 (begin
                    ((f ⊗ g) ∘ μ⁻¹) ∘ (μ ∘ (f⁻¹ ⊗ g⁻¹))
                  ≈⟨ cancelInner {i = μ} {μ⁻¹} μ⁻¹∘μ {f = f ⊗ g} {f⁻¹ ⊗ g⁻¹} ⟩
                    (f ⊗ g) ∘ (f⁻¹ ⊗ g⁻¹)
                  ≈⟨ ⊗-inverse {f = f⁻¹} {f} {g⁻¹} {g} f∘f⁻¹ g∘g⁻¹ ⟩
                    id
                  ∎)
                 (begin
                    (μ ∘ (f⁻¹ ⊗ g⁻¹)) ∘ ((f ⊗ g) ∘ μ⁻¹)
                  ≈⟨ cancelInner {i = f ⊗ g} {f⁻¹ ⊗ g⁻¹}
                       (⊗-inverse {f = f} {f⁻¹} {g} {g⁻¹} f⁻¹∘f g⁻¹∘g)
                       {f = μ} {μ⁻¹} ⟩
                    μ ∘ μ⁻¹ {a = m}
                  ≈⟨ μ∘μ⁻¹ {a = m} ⟩
                    id
                  ∎))
      }
     where
       open ≈-Reasoning
       -- 1↔⊤ will be in agda-stdlib 2.0, but only the level-monomorphic version.
       -- TODO: Add level-polymorphic versions.
       1↔⊤ : 𝔽 1 ↔ ⊤
       1↔⊤ = mk↔′ (λ { 0F → tt }) (λ { tt → 0F }) (λ { tt → refl≡ }) λ { 0F → refl≡ }

    productsH : ProductsH SetFinite ⟨→⟩
    productsH = record
                  { ε     = id
                  ; μ     = id
                  ; ε⁻¹   = id
                  ; μ⁻¹   = id
                  ; ε⁻¹∘ε = λ _ → refl≡
                  ; ε∘ε⁻¹ = λ _ → refl≡
                  ; μ⁻¹∘μ = λ _ → refl≡
                  ; μ∘μ⁻¹ = λ _ → refl≡
                  }

    -- TODO: Coproducts
    -- TODO: Exponentials

    2↔Bool : 𝔽 2 ↔ Bool
    2↔Bool = mk↔′ (two 𝕗 𝕥) (bool 0F 1F)
                  (λ { 𝕗  → refl≡ ; 𝕥  → refl≡ })
                  (λ { 0F → refl≡ ; 1F → refl≡ })

    boolean : Boolean SetFinite
    boolean = record { Bool = mk 2↔Bool }

    booleanH : BooleanH SetFinite ⟨→⟩
    booleanH = record { β = id ; β⁻¹ = id }

    strongBooleanH : StrongBooleanH SetFinite ⟨→⟩
    strongBooleanH = record { β⁻¹∘β = λ _ → refl≡ ; β∘β⁻¹ = λ _ → refl≡ }

-- Define the subcategory of ⟨→⟩ with homomorphisms and laws
open import Categorical.Subcategory ⟨→⟩ SetFinite public

