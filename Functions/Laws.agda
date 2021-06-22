{-# OPTIONS --safe --without-K #-}

module Functions.Laws where

open import Function.Equivalence hiding (id)

open import Categorical.Raw hiding (Category; Cartesian; CartesianClosed)
open import Categorical.Laws
open import Categorical.Equiv
open import Functions.Raw public
open import Axiom.Extensionality.Propositional

module →-laws-instances (extensionality : Extensionality _ _) where

  open import Level
  open import Data.Product using (_,_)
  open import Relation.Binary.PropositionalEquality
       renaming ( refl to refl≡
                ; trans to trans≡
                ; sym to sym≡
                )
  instance

    category : Category Function _
    category = record
      { identityˡ = refl≡
      ; identityʳ = refl≡
      ; assoc     = refl≡
      ; ∘≈        = λ { {k = k} h≈k f≈g → trans≡ h≈k (cong k f≈g) }
      }

    cartesian : Cartesian Function _
    cartesian = record
      { exl▵exr = refl≡
      ; ∀× = equivalence
          (λ k≈f▵g → (λ { {a} → cong exl k≈f▵g })
                   , (λ { {a} → cong exr k≈f▵g }))
          (λ { (exl∘k≈f , exr∘k≈g) {a} → cong₂ _,_ exl∘k≈f exr∘k≈g })
      ; ▵≈ = λ h≈k f≈g → cong₂ _,_ h≈k f≈g
      }

    cartesianClosed : CartesianClosed Function _
    cartesianClosed = record
      { ∀⇛ =
        equivalence
         (λ { g≈f {a , b} → sym≡ (trans≡ (cong (λ fbc → fbc b) g≈f) refl≡) })
         (λ { f≈uncurry-g {a} → extensionality λ _ →
                                  sym≡ (trans≡ (cong id f≈uncurry-g) refl≡) })
      ; curry≈ = λ f≡g → extensionality (λ _ → trans≡ f≡g refl≡)
      } 

    -- TODO: Logic
