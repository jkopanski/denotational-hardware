{-# OPTIONS --safe --without-K #-}
-- Free category

open import Categorical.Homomorphism
open import Categorical.Laws as L hiding (Category; Cartesian; CartesianClosed)

module Categorical.Free.Homomorphism
   {o}{obj : Set o}
   ⦃ _ : Products obj ⦄ ⦃ _ : Exponentials obj ⦄ ⦃ _ : Boolean obj ⦄
   {ℓ}(_↠_ : obj → obj → Set ℓ) {q} ⦃ equiv↠ : Equivalent q _↠_ ⦄
   ⦃ _ : Category _↠_ ⦄ ⦃ _ : Cartesian _↠_ ⦄ ⦃ _ : Logic _↠_ ⦄
 where

open import Ty

open import Categorical.Free.Raw public

private
  variable
    a b c d : Ty

module free-homomorphism-instances where

 private

   ⟦_⟧ : (a ⇨ b) → (Fₒ a ↠ Fₒ b)
   ⟦  `id   ⟧ =  id
   ⟦ g `∘ f ⟧ =  ⟦ g ⟧ ∘ ⟦ f ⟧
   ⟦   `!   ⟧ =  !
   ⟦ f `▵ g ⟧ =  ⟦ f ⟧ ▵ ⟦ g ⟧
   ⟦  `exl  ⟧ = exl
   ⟦  `exr  ⟧ = exr
   ⟦ `false ⟧ = false
   ⟦ `true  ⟧ = true 
   ⟦  `not  ⟧ = not 
   ⟦   `∧   ⟧ = ∧  
   ⟦   `∨   ⟧ = ∨  
   ⟦  `xor  ⟧ = xor 
   ⟦ `cond  ⟧ = cond

   infixr 1 _;↠_   -- unicode semicolon
   _;↠_ : ∀ {a b : obj} {f g h : a ↠ b} (f≈g : f ≈ g) (g≈h : g ≈ h) → f ≈ h
   _;↠_ = _;_

 instance

   H : Homomorphism _⇨_ _↠_
   H = record { Fₘ = ⟦_⟧ }

   equivalent : Equivalent q _⇨_
   equivalent = H-equiv

   open Equivalent equiv↠ using () renaming (refl to refl↠; sym to sym↠)

   categoryH : CategoryH _⇨_ _↠_
   categoryH = record
     { F-id = refl↠
     ; F-∘  = refl↠
     }

   cartesianH : ⦃ _ : L.Category _↠_ ⦄ → CartesianH _⇨_ _↠_
   cartesianH = record
     { F-!   = sym↠ identityˡ
     ; F-▵   = sym↠ identityˡ
     ; F-exl = identityʳ
     ; F-exr = identityʳ
     }

   open ≈-Reasoning
   open import Categorical.Reasoning

   logicH : ⦃ _ : L.Category _↠_ ⦄ ⦃ _ : L.Cartesian _↠_ ⦄ → LogicH _⇨_ _↠_
   logicH = record
              { F-false = identityʳ ;↠ sym↠ identityˡ
              ; F-true  = identityʳ ;↠ sym↠ identityˡ
              ; F-not   = identityʳ ;↠ sym↠ identityˡ
              ; F-∧     = ∘≈ʳ (identityˡ ;↠ id⊗id) ;↠ identityʳ ;↠ sym↠ identityˡ
              ; F-∨     = ∘≈ʳ (identityˡ ;↠ id⊗id) ;↠ identityʳ ;↠ sym↠ identityˡ
              ; F-xor   = ∘≈ʳ (identityˡ ;↠ id⊗id) ;↠ identityʳ ;↠ sym↠ identityˡ
              ; F-cond  = ∘≈ʳ (identityˡ ;↠ id⊗id) ;↠ identityʳ
              }
