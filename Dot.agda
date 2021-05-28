{-# OPTIONS --safe --without-K #-}
-- Generate GraphViz/Dot format from SSA

module Dot where

open import Function using () renaming (_∘′_ to _∘_)
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

private

  package : List String → String
  package = (_++ "\n}\n") ∘ ("digraph {" ++_) ∘ ("\n" ++_) ∘
            unlines ∘ mapᴸ (λ s → "  " ++ s ++ ";") ∘ (prelude ++ᴸ_)
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

  comp : ℕ → Statement → List String
  comp comp# (mk op {i} ins o) with #atoms i | #atoms o
  ... | zero | zero = []  -- drop disconnected components
  ... | _    | _    =
    (show comp# ++
     " [label=\"" ++
     braces (labelsⁱ i ++ op ++ labelsᵒ o) ++
     "\"]")
    ∷ toList (zipWith (λ x i → wire x (mk comp# i)) ins indices)

dot : SSA → String
dot = package ∘ concatᴸ ∘ mapℕ comp
