{-# OPTIONS --safe --without-K #-}
-- Free category

open import Categorical.Homomorphism
open import Categorical.Laws as L
       hiding (Category; Cartesian; CartesianClosed; Logic)

module Categorical.Free.Laws
         {o}{obj : Set o} ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄
         (_↠_ : obj → obj → Set o) {q} ⦃ equiv↠ : Equivalent q _↠_ ⦄
         ⦃ _ : Category _↠_ ⦄ ⦃ _ : Cartesian _↠_ ⦄ ⦃ _ : Logic _↠_ ⦄
         ⦃ _ : L.Category _↠_ ⦄ ⦃ _ : L.Cartesian _↠_ ⦄
 where

import Categorical.Laws as L

open import Categorical.Free.Homomorphism _↠_ public

module free-law-instances where

 instance

    open import Categorical.MakeLawful _⇨_ _↠_

    category : L.Category _⇨_
    category = LawfulCategoryᶠ

    -- TODO: Cartesian. Also logic when we have laws.
