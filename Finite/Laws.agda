{-# OPTIONS --safe --without-K #-}
module Finite.Laws where

open import Level using (0ℓ)

open import Categorical.Homomorphism
open import Categorical.Laws as L hiding (Category; Cartesian; CartesianClosed)

open import Functions 0ℓ

open import Finite.Homomorphism

module finite-law-instances where

 instance

    open import Categorical.MakeLawful _⇨_ ⟨→⟩

    category : L.Category _⇨_
    category = LawfulCategoryᶠ

    -- TODO: Cartesian when we have LawfulCartesianᶠ
