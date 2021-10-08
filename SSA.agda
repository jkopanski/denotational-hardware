{-# OPTIONS --safe --without-K #-}

-- Generate static single assignment form from linearized morphism.

module SSA where

open import Data.Product using (_,_)
open import Data.Nat using (ℕ; suc; zero)
open import Data.String hiding (toList; show)
open import Data.List using (List; []; [_]; _∷_; upTo; reverse; _∷ʳ_)
       renaming (length to lengthᴸ; zipWith to zipWithᴸ; map to mapᴸ)

open import Categorical.Raw
open import Functions.Raw
open import Show

open import Ty
open import Index
open import Primitive.Type renaming (_⇨_ to _⇨ₚ_)
open import Routing.Type renaming (_⇨_ to _⇨ᵣ_)
open import Linearize.Type Function _⇨ₚ_ _⇨ᵣ_ renaming (_⇨_ to _⇨ₖ_)

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

mutual

  record Statement : Set where
    inductive
    constructor mk
    field
      comp# : ℕ
      op : String
      {i} : Ty
      ins : Ref i
      o   : Ty

  SSA : Set
  SSA = List Statement

  stat : ∀ {i}{o} → ℕ → (i ⇨ₚ o) → Ref i → Statement
  stat {i}{o} comp# p r = mk comp# (show p) r o

  mk′ : ∀ {i}{o} → ℕ → (i ⇨ₚ o) → Ref i → Statement × ℕ
  mk′ {i}{o} comp# p r = first (λ op → mk comp# (show p) r o) (p , suc comp#)

  refs : ℕ → Ref b
  refs comp# = tabulate′ (mk comp#)

  ssa : (a ⇨ₖ b) → SSA
  ssa f = exl (ssa′ 0 f)

  ssa′ : ℕ → (a ⇨ₖ b) → SSA × ℕ
  ssa′ {a} comp# f = ssaᵏ (suc comp#) (refs comp#) f [ mk comp# "In" † a ]
   where
    ssaᵏ : ∀ {a b} → ℕ → Ref a → (a ⇨ₖ b) → List Statement → SSA × ℕ
    ssaᵏ comp# ins ⌞ r ⌟ ss =
      reverse (mk comp# "Out" (⟦ r ⟧′ ins) ⊤ ∷ ss) , suc comp#
    ssaᵏ comp# ins (f ∘·first p ∘ r) ss with ⟦ r ⟧′ ins ; ... | x ､ y =
      ssaᵏ (suc comp#) (refs comp# ､ y) f (stat comp# p x ∷ ss)

instance
  Show-Id : Show (Id z)
  Show-Id = record { show = λ (mk comp# j) → "x" ++ show comp# ++ show j }

private
 
  indent-lines : String → String
  indent-lines = unlines ∘ mapᴸ ("  " ++_) ∘ lines

  mutual

    show-Stmt : Statement → String
    show-Stmt (mk comp# op ins o) =
      show (refs {o} comp#) ++ " = " ++ op ++ " "
              ++ parensIfSpace (show ins)

    show-SSA : SSA → String
    show-SSA ssa = -- unlines (mapᴸ show-Stmt ssa)  -- termination check :(
                   unlines (show-SSA′ ssa)
     where
       show-SSA′ : SSA → List String
       show-SSA′ [] = []
       show-SSA′ (s ∷ ss) = show-Stmt s ∷ show-SSA′ ss

instance

  Show-Stmt : Show Statement
  Show-Stmt = record { show = show-Stmt }

  Show-SSA : Show SSA
  Show-SSA = record { show = show-SSA }

-- TODO: sort out what to make private.
