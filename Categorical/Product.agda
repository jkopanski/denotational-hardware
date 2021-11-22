{-# OPTIONS --safe --without-K #-}
-- Product of categories

-- TODO: Maybe move to Categorical.Construct.Product

open import Categorical.Raw
open import Categorical.Homomorphism

module Categorical.Product
  {o₁} {obj₁ : Set o₁} {ℓ₁} (_⇨₁_ : obj₁ → obj₁ → Set ℓ₁) ⦃ _ : Category _⇨₁_ ⦄
  {o₂} {obj₂ : Set o₂} {ℓ₂} (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂) ⦃ _ : Category _⇨₂_ ⦄
 where

open import Level using (_⊔_)
open import Data.Product using (_,_; proj₁; proj₂) renaming (_×_ to _×′_)

private
  Obj = obj₁ ×′ obj₂

record _⇨_ (a b : Obj) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor mk
  field
    f₁ : proj₁ a ⇨₁ proj₁ b
    f₂ : proj₂ a ⇨₂ proj₂ b

-- TODO: Is there a pattern-matching alternative to the proj'shere?

module product-instances where

 instance

  category : Category _⇨_
  category = record { id = mk id id ; _∘_ = λ (mk g₁ g₂) (mk f₁ f₂) → mk (g₁ ∘ f₁) (g₂ ∘ f₂) }

  products : ⦃ _ : Products obj₁ ⦄ ⦃ _ : Products obj₂ ⦄ → Products Obj
  products = record { ⊤ = ⊤ , ⊤ ; _×_ = λ (a₁ , a₂) (b₁ , b₂) → (a₁ × b₁) , (a₂ × b₂) }

  cartesian : ⦃ _ : Products obj₁ ⦄ ⦃ _ : Products obj₂ ⦄
              ⦃ _ : Cartesian _⇨₁_ ⦄ ⦃ _ : Cartesian _⇨₂_ ⦄ →
              Cartesian _⇨_
  cartesian = record
    {  !  = mk ! !
    ; _▵_ = λ (mk f₁ f₂) (mk g₁ g₂) → mk (f₁ ▵ g₁) (f₂ ▵ g₂)
    ; exl = mk exl exl
    ; exr = mk exr exr
    }

  boolean : ⦃ _ : Boolean obj₁ ⦄ ⦃ _ : Boolean obj₂ ⦄ → Boolean Obj
  boolean = record { Bool = Bool , Bool }

  logic : ⦃ _ : Products obj₁ ⦄ ⦃ _ : Products obj₂ ⦄
          ⦃ _ : Boolean  obj₁ ⦄ ⦃ _ : Boolean  obj₂ ⦄
          ⦃ _ : Logic _⇨₁_ ⦄ ⦃ _ : Logic _⇨₂_ ⦄
        → Logic _⇨_
  logic = record
            { false = mk false false
            ; true  = mk true  true
            ; not   = mk  not   not
            ; ∧     = mk   ∧     ∧
            ; ∨     = mk   ∨     ∨
            ; xor   = mk  xor   xor
            ; cond  = mk cond  cond
            }

  equivalent : ∀ {q₁} ⦃ _ : Equivalent q₁ _⇨₁_ ⦄ {q₂} ⦃ _ : Equivalent q₂ _⇨₂_ ⦄
             → Equivalent (q₁ ⊔ q₂) _⇨_
  equivalent = record
    { _≈_ = λ (mk f₁ f₂) (mk g₁ g₂) → f₁ ≈ g₁ ×′ f₂ ≈ g₂  -- Does this construction already exist?
    ; equiv = record
       { refl  = refl , refl
       ; sym   = λ (eq₁ , eq₂) → sym eq₁ , sym eq₂
       ; trans = λ (eq₁ , eq₂) (eq₁′ , eq₂′)  → trans eq₁ eq₁′ , trans eq₂ eq₂′
       }
    }

  open import Categorical.Laws as L hiding (Category; Cartesian; CartesianClosed; Logic)

  l-category : ∀ {q₁} ⦃ _ : Equivalent q₁ _⇨₁_ ⦄ {q₂} ⦃ _ : Equivalent q₂ _⇨₂_ ⦄
               ⦃ _ : L.Category _⇨₁_ ⦄ ⦃ _ : L.Category _⇨₂_ ⦄
             → L.Category _⇨_
  l-category = record
    { identityˡ = identityˡ , identityˡ
    ; identityʳ = identityʳ , identityʳ
    ; assoc = assoc , assoc
    ; ∘≈ = λ (eq₁ , eq₂) (eq₁′ , eq₂′) → ∘≈ eq₁ eq₁′ , ∘≈ eq₂ eq₂′
    }

  open import Function.Equivalence
  open import Function.Equality as F using (Π; _⟨$⟩_)

  l-cartesian : ∀ {q₁} ⦃ _ : Equivalent q₁ _⇨₁_ ⦄ {q₂} ⦃ _ : Equivalent q₂ _⇨₂_ ⦄
                ⦃ _ :   Products  obj₁ ⦄ ⦃ _ :   Products  obj₂ ⦄
                ⦃ _ :   Cartesian _⇨₁_ ⦄ ⦃ _ :   Cartesian _⇨₂_ ⦄
                ⦃ _ : L.Category  _⇨₁_ ⦄ ⦃ _ : L.Category  _⇨₂_ ⦄
                ⦃ _ : L.Cartesian _⇨₁_ ⦄ ⦃ _ : L.Cartesian _⇨₂_ ⦄
             → L.Cartesian _⇨_
  l-cartesian = record
    { ∀⊤ = ∀⊤ , ∀⊤
    ; ∀× = λ { {a = a₁ , a₂} {b = b₁ , b₂} {c = c₁ , c₂} {f = mk f₁ f₂} {g = mk g₁ g₂} {k = mk k₁ k₂} →
        let e₁ = ∀× {f = f₁} {g₁} {k₁}
            e₂ = ∀× {f = f₂} {g₂} {k₂}
            module Q₁ = Equivalence e₁
            module Q₂ = Equivalence e₂
            h₁ = Q₁.to ⟨$⟩_ ; h₁⁻¹ = Q₁.from ⟨$⟩_
            h₂ = Q₂.to ⟨$⟩_ ; h₂⁻¹ = Q₂.from ⟨$⟩_
        in
        equivalence
          (λ (z₁ , z₂) → let eq₁ , eq₁′ = h₁ z₁ ; eq₂ , eq₂′ = h₂ z₂ in
            (eq₁ , eq₂) , (eq₁′ , eq₂′)
            )
          (λ ((eq₁ , eq₂) , (eq₁′ , eq₂′)) →
            h₁⁻¹ (eq₁ , eq₁′) , h₂⁻¹ (eq₂ , eq₂′))
      }
    ; ▵≈ = λ { {f = mk f₁ f₂} {g = mk g₁ g₂} {h = mk h₁ h₂} {k = mk k₁ k₂}
               (h₁≈k₁ , h₂≈k₂) (f₁≈g₁ , f₂≈g₂) →
                 (▵≈ h₁≈k₁ f₁≈g₁) , ▵≈ h₂≈k₂ f₂≈g₂ }
    }

  l-logic : ∀ {q₁} ⦃ _ : Equivalent q₁ _⇨₁_ ⦄ {q₂} ⦃ _ : Equivalent q₂ _⇨₂_ ⦄
            ⦃ _ : Products  obj₁ ⦄ ⦃ _ : Products  obj₂ ⦄
            ⦃ _ : Boolean   obj₁ ⦄ ⦃ _ : Boolean   obj₂ ⦄
            ⦃ _ : Cartesian _⇨₁_ ⦄ ⦃ _ : Cartesian _⇨₂_ ⦄
            ⦃ _ :    Logic  _⇨₁_ ⦄ ⦃ _ :    Logic  _⇨₂_ ⦄
            ⦃ _ :  L.Logic  _⇨₁_ ⦄ ⦃ _ :  L.Logic  _⇨₂_ ⦄
          → L.Logic _⇨_
  l-logic = record { f∘cond = f∘cond , f∘cond }

  -- Homomorphisms

  Hₒ₁ : Homomorphismₒ Obj obj₁
  Hₒ₁ = record { Fₒ = proj₁ }

  H₁ : Homomorphism _⇨_ _⇨₁_
  H₁ = record { Fₘ = λ (mk f₁ f₂) → f₁ }

  Hₒ₂ : Homomorphismₒ Obj obj₂
  Hₒ₂ = record { Fₒ = proj₂ }

  H₂ : Homomorphism _⇨_ _⇨₂_
  H₂ = record { Fₘ = λ (mk f₁ f₂) → f₂ }

  categoryH₁ : ∀ {q₁} ⦃ _ : Equivalent q₁ _⇨₁_ ⦄ → CategoryH _⇨_ _⇨₁_
  categoryH₁ = record { F-id = refl ; F-∘ = refl }

  categoryH₂ : ∀ {q₂} ⦃ _ : Equivalent q₂ _⇨₂_ ⦄ → CategoryH _⇨_ _⇨₂_
  categoryH₂ = record { F-id = refl ; F-∘ = refl }
