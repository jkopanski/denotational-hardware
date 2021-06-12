{-# OPTIONS --safe --without-K #-}

module Functions.Laws where

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
      ; ∀▵ =
        equivalence
          (λ k≈f▵g
           → (λ { {a} → cong exl k≈f▵g })
           , (λ { {a} → cong exr k≈f▵g })
          )
          (λ { (proj₁∘k≈f , proj₂∘k≈g) {a}
           → cong₂ _,_ proj₁∘k≈f proj₂∘k≈g
             }
          )
      ; ▵≈ = λ h≈k f≈g → cong₂ _,_ h≈k f≈g
      } where open import Function.Equivalence
              open import Categorical.Raw

    cartesianClosed : CartesianClosed Function _
    cartesianClosed = record
      { ∀-exp =
        equivalence
         (λ { k≡f {a , b}
          → sym≡ (trans≡ (cong (λ fbc → fbc b) k≡f) refl≡)
            }
         )
         (λ { f≡uncurry-k {a}
          → extensionality
             (λ _ → sym≡ (trans≡ (cong id f≡uncurry-k) refl≡))
            }
         )
      ; curry≈ = λ f≡g → extensionality (λ _ → trans≡ f≡g refl≡)
      } where open import Function.Equivalence hiding (id)
              open import Categorical.Raw

    -- TODO: Logic
