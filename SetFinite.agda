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

open import Finite renaming (_⇨_ to _↠_; mk to mk↠)

-- A finite set, demonstrated by a number n and proof that A ≅ 𝔽 n.
record SetFinite : Set₁ where
  constructor mkS               -- TODO: rename later
  field
    { A } : Set
    { n } : ℕ
    iso : A ↔ 𝔽 n

private

    pattern mk↔″ f f⁻¹ f∘f⁻¹ f⁻¹∘f =
      record { f = f ; f⁻¹ = f⁻¹ ; inverse = f∘f⁻¹ , f⁻¹∘f }

module SetFinite-Set-instances where

  instance

    open import Categorical.Reasoning

    Hₒ : Homomorphismₒ SetFinite Set
    Hₒ = record { Fₒ = SetFinite.A }

    products : Products SetFinite
    products = record
      { ⊤ = mkS (mk↔′ ε ε⁻¹ ε∘ε⁻¹ ε⁻¹∘ε)
      ; _×_ = λ (mkS {A} {m} (mk↔″ f f⁻¹ f∘f⁻¹ f⁻¹∘f))
                (mkS {B} {n} (mk↔″ g g⁻¹ g∘g⁻¹ g⁻¹∘g)) →
                let open ≈-Reasoning in
         mkS {A × B} {m × n}
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
           )  -- TODO: simplify with a monoidal category of isomorphisms.
      }

    productsH : ProductsH SetFinite ⟨→⟩
    productsH = record { ε     = id
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
    boolean = record { Bool = mkS (mk↔′ β β⁻¹ β∘β⁻¹ β⁻¹∘β) }

    booleanH : BooleanH SetFinite ⟨→⟩
    booleanH = record { β = id ; β⁻¹ = id }

    strongBooleanH : StrongBooleanH SetFinite ⟨→⟩
    strongBooleanH = record { β⁻¹∘β = λ _ → refl ; β∘β⁻¹ = λ _ → refl }

-- Define the subcategory of ⟨→⟩ with homomorphisms and laws
open import Categorical.Subcategory ⟨→⟩ SetFinite public


module SetFinite-ℕ-instances where

  instance

    Hₒ : Homomorphismₒ SetFinite ℕ
    Hₒ = record { Fₒ = SetFinite.n }

    productsH : ProductsH SetFinite _↠_
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

    booleanH : BooleanH SetFinite _↠_
    booleanH = record { β = id ; β⁻¹ = id }

    strongBooleanH : StrongBooleanH SetFinite _↠_
    strongBooleanH = record { β⁻¹∘β = λ _ → refl ; β∘β⁻¹ = λ _ → refl }

    H : Homomorphism _⇨_ _↠_
    H = record { Fₘ = λ {
      {mkS (mk↔″ _ fin₁⁻¹ _ _)} {mkS (mk↔″ fin₂ _ _ _)} (mk g) → mk↠ (fin₂ ∘ g ∘ fin₁⁻¹) } }

    categoryH : CategoryH _⇨_ _↠_
    categoryH = record
      { F-id = λ { {a = mkS {A} {n} (mk↔″ fin fin⁻¹ fin∘fin⁻¹ _)} x →
                   begin
                     fin (id (fin⁻¹ x))
                   ≡⟨⟩
                     fin (fin⁻¹ x)
                   ≡⟨ fin∘fin⁻¹ x ⟩
                     x
                   ∎
                 }
      ; F-∘ = λ { {b = mkS (mk↔″ fin₂ fin⁻¹₂ _ fin⁻¹∘fin₂)}
                  {c = mkS (mk↔″ fin₃ _ _ _)}
                  {a = mkS (mk↔″ _ fin⁻¹₁ _ _)}
                  {g = mk g} {mk f} x →
                  begin
                    fin₃ (g (f (fin⁻¹₁ x)))
                  ≡˘⟨ cong (fin₃ ∘ g) (fin⁻¹∘fin₂ (f (fin⁻¹₁ x))) ⟩
                    fin₃ (g (fin⁻¹₂ (fin₂ (f (fin⁻¹₁ x)))))
                  ∎
                }
      } where open import Relation.Binary.PropositionalEquality
              open ≡-Reasoning

-- We could now define a subcategory of Finite.
