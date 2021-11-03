{-# OPTIONS --safe --without-K #-}
-- Representation counterpart to the Finite category

module TFinite where

open import Level using (0ℓ)
open import Data.Nat
open import Data.Fin hiding (_+_; #_)
open import Data.Product using (_,_)

open import Categorical.Equiv
open import Categorical.Homomorphism hiding (uncurry)
open import Categorical.Laws

open import Functions 0ℓ

infixr 2 _`×_
data Ty : Set where
  `⊤    : Ty
  `Bool : Ty
  _`×_  : Ty → Ty → Ty

-- TODO: Possibly add _`⇛_  : Ty → Ty → Ty

open import Finite renaming (_⇨_ to _↠_)

open import Relation.Binary.PropositionalEquality
  using (cong; cong₂) renaming (refl to refl≡)

module tfinite-instances where

  instance

    Hₒ : ∀ {o}{obj : Set o} ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄ →
         Homomorphismₒ Ty obj
    Hₒ {obj = obj} = record { Fₒ = h }
      where
        h : Ty → obj
        h   `⊤     = ⊤
        h  `Bool   = Bool
        h (a `× b) = h a × h b

    -- Note: for obj = ℕ, Fₒ t computes the cardinality of ⟦ t ⟧

    products : Products Ty
    products = record { ⊤ = `⊤ ; _×_ = _`×_ }

    productsH : ProductsH Ty _↠_
    productsH = record
                  { ε     = mk id
                  ; μ     = mk id
                  ; ε⁻¹   = mk id
                  ; μ⁻¹   = mk id
                  ; ε⁻¹∘ε = λ _ → refl≡
                  ; ε∘ε⁻¹ = λ _ → refl≡
                  ; μ⁻¹∘μ = λ _ → refl≡
                  ; μ∘μ⁻¹ = λ _ → refl≡
                  }

    -- TODO: Coproducts
    -- TODO: Exponentials

    boolean : Boolean Ty
    boolean = record { Bool = `Bool }

    booleanH : BooleanH Ty ⟨→⟩
    booleanH = record { β = id ; β⁻¹ = id }

    strongBooleanH : StrongBooleanH Ty ⟨→⟩
    strongBooleanH = record { β⁻¹∘β = λ _ → refl≡ ; β∘β⁻¹ = λ _ → refl≡ }

-- Define the subcategory of Ty with homomorphisms and laws
open import Categorical.Subcategory _↠_ Ty public


open import Categorical.Reasoning

⟦_⟧ : Ty → Set
⟦ `⊤ ⟧ = ⊤
⟦ `Bool ⟧ = Bool
⟦ s `× t ⟧ = ⟦ s ⟧ × ⟦ t ⟧

private variable s t : Ty

-- ⟦_⟧ = Fₒ

# : Ty → ℕ
# = Fₒ

-- TODO: Why doesn't ⟦_⟧ = Fₒ work out?

fin : ⟦ t ⟧ → Fin (# t)
fin {`⊤} = ε
fin {`Bool} = β
fin {s `× t} = μ ∘ (fin ⊗ fin)

fin² : ⟦ s ⟧ × ⟦ t ⟧ → Fin (# s) × Fin (# t)
fin² = fin ⊗ fin

fin⁻¹ : Fin (# t) → ⟦ t ⟧
fin⁻¹ {`⊤} = ε⁻¹
fin⁻¹ {`Bool} = β⁻¹
fin⁻¹ {s `× t} = (fin⁻¹ ⊗ fin⁻¹) ∘ μ⁻¹

fin⁻¹∘fin : fin⁻¹ ∘ fin {t} ≈ id
fin⁻¹∘fin {`⊤} = ε⁻¹∘ε
fin⁻¹∘fin {`Bool} = β⁻¹∘β

fin⁻¹∘fin {s `× t} =
  begin
    fin⁻¹ ∘ fin
  ≡⟨⟩
    ((fin⁻¹ ⊗ fin⁻¹) ∘ μ⁻¹) ∘ μ ∘ (fin ⊗ fin)
  ≡⟨⟩
    (fin⁻¹ ⊗ fin⁻¹) ∘ μ⁻¹ ∘ μ ∘ (fin ⊗ fin)
  ≡⟨⟩
    (fin⁻¹ ⊗ fin⁻¹) ∘ (μ⁻¹ ∘ μ) ∘ (fin ⊗ fin)
  ≈⟨ (λ (x , y) → cong (fin⁻¹ ⊗ fin⁻¹) (μ⁻¹∘μ (fin x , fin y))) ⟩
    (fin⁻¹ ⊗ fin⁻¹) ∘ (fin ⊗ fin)
  ≡⟨⟩
    (λ (x , y) → fin⁻¹ (fin x) , fin⁻¹ (fin y))
  ≈⟨ (λ (x , y) → cong₂ _,_ (fin⁻¹∘fin x) (fin⁻¹∘fin y)) ⟩
    (λ (x , y) → x , y)
  ≡⟨⟩
    id
  ∎
 where open ≈-Reasoning

-- TODO: Simplify proof. Try using ⊗-inverse

-- I haven't yet needed fin⁻¹∘fin or fin∘fin⁻¹.
