{-# OPTIONS --safe --without-K #-}

open import Level

open import Categorical.Raw
open import Categorical.Equiv
open import Categorical.Laws as L hiding (Category)
open import Categorical.Homomorphism

module Encode.Homomorphism
         {o} {obj : Set o}
         {ℓ} (_↠_ : obj → obj → Set ℓ) ⦃ _ : Category _↠_ ⦄
         q ⦃ _ : Equivalent q _↠_ ⦄
         {o′} {obj′ : Set o′} (⟦_⟧ : obj′ → obj)
         ⦃ _ : L.Category _↠_ q ⦄
 where

open import Encode.Raw _↠_ q ⟦_⟧ public

instance

  open import Categorical.Homomorphism

  categoryH : CategoryH _⇨_ _↠_ q
  categoryH = record { F-id = refl ; F-∘ = refl }

  -- Also CartesianH, CartesianClosedH, and LogicH

-- TODO: Show that Encode.Type itself (mapping _↠_ to _⇨_) is a functor etc.
