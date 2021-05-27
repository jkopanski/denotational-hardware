-- Miscellaneous circuit examples

module Test where

open import Level
open import Data.String hiding (show)
open import IO

open import Show
open import Categorical.Raw
open import Functions.Raw
open import Ty
open import Index
open import Primitive.Raw Function renaming (_⇨_ to _⇨ₚ_)
open import Routing.Raw renaming (_⇨_ to _⇨ᵣ_)
open import Linearize.Raw Function _⇨ₚ_ _⇨ᵣ_ renaming (_⇨_ to _⇨ₖ_)

open import SSA
open import Dot

-- TODO: trim imports

open import Examples.Add

example : ∀ {i o : Ty} → String → (i ⇨ₖ o) → IO {0ℓ} _
example name f =
  do putStrLn name
     save ".ssa" (show s)
     save ".dot" d
 where
   save : String → String → IO {0ℓ} _
   save ext str = writeFile ("Figures/" ++ name ++ ext) str
   s = ssa f
   d = dot s

main = run do

  example "id-Bool"   (id {a = Bool})
  example "id-Bool2"  (id {a = Bool × Bool})
  example "not"       not
  example "and"       ∧
  example "nand"      (not ∘ ∧)
  example "first-not" (first {b = V Bool 2} not)

  -- example "shiftR-swap-c5" (ce.shiftR-swap {5})
  -- example "lfsr-c5"  ce.lfsr₅

  example "half-add"     halfAdd
  example "full-add"     fullAdd
  example "ripple-add-4" (rippleAdd 4)
  example "ripple-add-8" (rippleAdd 8)

  example "carry-select-3x5" (carrySelect 3 5)
  example "carry-select-4x4" (carrySelect 4 4)
  example "carry-select-8x8" (carrySelect 8 8)
  example "carry-select-16x16" (carrySelect 16 16)
