{-# OPTIONS --safe --without-K #-}

-- Generate static single assignment form from linearized morphism.

-- To insert before Dot.

module SSA where

open import Level using (0ℓ) -- temp?
open import Data.Product using (_,_)
open import Data.Nat using (ℕ; suc; zero)
open import Data.String hiding (toList; show)
open import Data.List using (List; []; [_]; _∷_; upTo; reverse; _∷ʳ_)
       renaming (length to lengthᴸ; zipWith to zipWithᴸ)

open import Categorical.Raw
open import Functions.Raw
open import Show

open import Ty
open import Index
open import Primitive.Type renaming (_⇨_ to _⇨ₚ_)
open import Routing.Type renaming (_⇨_ to _⇨ᵣ_)
open import Linearize.Type {objₘ = Set} Function _⇨ₚ_ _⇨ᵣ_ renaming (_⇨_ to _⇨ₖ_)

private variable a b z : Ty

-- Identifier as component/instance number and output index
record Id (z : Ty) : Set where
  constructor mk
  field
    comp# : ℕ
    {o} : Ty
    j : Index z o

-- An identifier for each index in a Ty
Ref : Ty → Set
Ref = Indexed Id

record Statement : Set where
  constructor mk
  field
    prim : String
    {i}  : Ty
    ins  : Ref i
    o    : Ty

mk′ : ∀ {i}{o} → (i ⇨ₚ o) → Ref i → Statement
mk′ {o = o} p r = mk (show p) r o

SSA : Set
SSA = List Statement

-- record SSA : Set where
--   constructor mk
--   field
--     ss : List Statement

refs : ℕ → Ref b
refs comp# = tabulate′ (mk comp#)

ssaᵏ : ℕ → Ref a → (a ⇨ₖ b) → List Statement → SSA
ssaᵏ _ ins ⌞ r ⌟ ss = reverse (mk "Out" (⟦ r ⟧′ ins) ⊤ ∷ ss)
ssaᵏ comp# ins (f ∘·first p ∘ r) ss with ⟦ r ⟧′ ins ; ... | x ､ y =
  ssaᵏ (suc comp#) (refs comp# ､ y) f (mk′ p x ∷ ss)

ssa : (a ⇨ₖ b) → SSA
ssa {a} f = ssaᵏ 1 (refs 0) f [ mk "In" · a ]

mapℕ : {A B : Set} → (ℕ → A → B) → List A → List B
mapℕ f as = zipWithᴸ f (upTo (lengthᴸ as)) as

instance

  Show-Id : ∀ {z} → Show (Id z)
  Show-Id = record {show = λ (mk comp# j) → "x" ++ show comp# ++ show j}

  Show-Stmt : Show (ℕ × Statement)
  Show-Stmt = record { show = 
    λ (comp# , mk prim ins o) →
      show (refs {o} comp#) ++ " = " ++ prim ++ " " ++ parensIfSpace (show ins)
   }

  Show-SSA : Show SSA
  Show-SSA = record { show = unlines ∘ mapℕ (curry show) }

-- TODO: sort out what to make private.
