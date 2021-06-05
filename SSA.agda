{-# OPTIONS --safe --without-K #-}

-- Generate static single assignment form from linearized morphism.

module SSA where

open import Level using (0ℓ) -- temp?
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
      op : Op
      {i} : Ty
      ins : Ref i
      o   : Ty

  SSA : Set
  SSA = List Statement

  data Op : Set where
    primₒ : String → Op
    applyₒ : Op
    curryₒ : SSA → Op

  mk′ : ∀ {i}{o} → ℕ → (i ⇨ᵤ o) → Ref i → Statement × ℕ
  mk′ {i}{o} comp# u r = first (λ op → mk comp# op r o) (mkOp u)
   where
     next = suc comp#
     mkOp : (i ⇨ᵤ o) → Op × ℕ
     mkOp (`prim p)  = primₒ (show p) , next
     mkOp `apply     = applyₒ , next
     mkOp (`curry f) = first curryₒ (ssa′ next f)

  refs : ℕ → Ref b
  refs comp# = tabulate′ (mk comp#)

  ssa : (a ⇨ₖ b) → SSA
  ssa f = exl (ssa′ 1 f)

  ssa′ : ℕ → (a ⇨ₖ b) → SSA × ℕ
  ssa′ {a} prim# f = ssaᵏ 1 (refs 0) f [ mk 0 (primₒ "In") † a ]
   where
    ssaᵏ : ∀ {a b} → ℕ → Ref a → (a ⇨ₖ b) → List Statement → SSA × ℕ
    ssaᵏ comp# ins ⌞ r ⌟ ss = reverse (mk comp# (primₒ "Out") (⟦ r ⟧′ ins) ⊤ ∷ ss) , suc comp#
    ssaᵏ comp# ins (f ∘·first u ∘ r) ss with ⟦ r ⟧′ ins
    ... | x ､ y with mk′ comp# u x
    ...            | s , comp#′ =
      ssaᵏ comp#′ (refs comp# ､ y) f (s ∷ ss)

instance
  Show-Id : Show (Id z)
  Show-Id = record { show = λ (mk comp# j) → "x" ++ show comp# ++ show j }

private
 
  indent-lines : String → String
  indent-lines = unlines ∘ mapᴸ ("  " ++_) ∘ lines

  mutual

    show-Op : Op → String
    show-Op (primₒ s) = s
    show-Op applyₒ = "apply"
    show-Op (curryₒ f) =
      "curry " ++ parensIfSpace ("\n" ++ indent-lines (show-SSA f))

    show-Stmt : Statement → String
    show-Stmt (mk comp# op ins o) =
      show (refs {o} comp#) ++ " = " ++ show-Op op ++ " "
              ++ parensIfSpace (show ins)

    show-SSA : SSA → String
    show-SSA ssa = -- unlines (mapᴸ show-Stmt ssa)  -- termination check :(
                   unlines (show-SSA′ ssa)
     where
       show-SSA′ : SSA → List String
       show-SSA′ [] = []
       show-SSA′ (s ∷ ss) = show-Stmt s ∷ show-SSA′ ss

instance

  Show-Op : Show Op
  Show-Op = record { show = show-Op }

  Show-Stmt : Show Statement
  Show-Stmt = record { show = show-Stmt }

  Show-SSA : Show SSA
  Show-SSA = record { show = show-SSA }

-- TODO: sort out what to make private.
