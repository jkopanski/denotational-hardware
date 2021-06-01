{-# OPTIONS --safe --without-K #-}
-- Generate GraphViz/Dot format from SSA

module Dot where

open import Function using (case_of_) renaming (_∘′_ to _∘_)
open import Data.Product using (_,_; curry; uncurry)
open import Data.String hiding (show; length; toList)
open import Data.List renaming (_++_ to _++ᴸ_; concat to concatᴸ; map to mapᴸ)
      hiding (intersperse; zipWith)
open import Data.Nat

open import Show
open import Ty
open import Index
open import SSA

private variable a b z : Ty

-- private

nest : List String → String
nest = (_++ "\n}") ∘ ("{\n" ++_) ∘
          unlines ∘ mapᴸ (λ s → "  " ++ s ++ ";")

-- TODO: Try dropping the semicolons.

package : List String → String
package = ("digraph " ++_) ∘ nest ∘ (prelude ++ᴸ_)
 where
   prelude : List String
   prelude =
     "margin=0" ∷
     "rankdir=LR" ∷
     "node [shape=Mrecord]" ∷
     "bgcolor=transparent" ∷
     "nslimit=20" ∷
     "ranksep=0.75" ∷
     []

subgraph : List String → String
subgraph = ("subgraph " ++_) ∘ nest ∘ (prelude ++ᴸ_)
 where
   prelude : List String
   prelude =
    "margin=8" ∷
    "fontsize=20" ∷
    "labeljust=r" ∷
    "color=DarkGreen" ∷
    []

-- 1 [label="{{<In0>|<In1>}|⊕|{<Out0>}}"];
-- 0:Out1 -> 0:In0;
-- 0:Out2 -> 0:In1;

labels : String → (String → String) → Ty → String
labels tag f a with #atoms a
... | zero = ""   -- No braces or "|", to avoid port appearance
... | suc _ = f (braces (intersperse "|" (toList (
        map (λ i → "<" ++ tag ++ show i ++ ">") (indices {a})))))

labelsⁱ : Ty → String
labelsⁱ = labels "In" (_++ "|")

labelsᵒ : Ty → String
labelsᵒ = labels "Out" ("|" ++_)

port : String → Id z → String
port dir (mk comp i) = show comp ++ ":" ++ dir ++ show i

wire : Id z → Id z → String
wire src dst = port "Out" src ++ " -> " ++  port "In" dst

comp′ : ℕ → String → (i : Ty) → Ref i → Ty → List String
comp′ comp# p i ins o with #atoms i + #atoms o
... | zero = []  -- drop disconnected components
... | _    =
  (show comp# ++
   " [label=\"" ++
   braces (labelsⁱ i ++ p ++ labelsᵒ o) ++  -- TODO: Change show op
   "\"]")
  ∷ toList (zipWith (λ x i → wire x (mk comp# i)) ins indices)

comp : Statement → List String
comp (mk comp# op {i} ins o) = comp′ comp# name i ins o ++ᴸ subs
 where
   name : String
   name = case op of λ
     { (primₒ str) → str ; applyₒ → "apply" ; (curryₒ f) → "" }

   subs : List String
   subs = case op of λ
     { (primₒ _) → []
     ; applyₒ → []
     ; (curryₒ f) → -- subgraph (concatᴸ (mapᴸ comp f)) ∷ []  -- termination
                    subgraph (concatᴸ (mapᴸ-comp f)) ∷ []
     } where mapᴸ-comp : SSA → List (List String)
             mapᴸ-comp [] = []
             mapᴸ-comp (s ∷ ss) = comp s ∷ mapᴸ-comp ss

-- TODO: How can I persuade the termination checker that the "mapᴸ comp f" form
-- terminates?

dot : SSA → String
dot = package ∘ concatᴸ ∘ mapᴸ comp
