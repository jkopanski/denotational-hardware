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
open import Categorical.Object
open import Ty
open import Primitive.Type
open import Index
-- open import Routing.Functor renaming (map to mapᵀ)
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

  labels : String → (String → String) → ℕ → String
  labels tag f n with n
  ... | zero = ""   -- No braces or "|", to avoid port appearance
  ... | suc _ = f (braces (
   intersperse "|" (mapᴸ (λ i → "<" ++ tag ++ show i ++ ">") (upTo n))))

  labelsⁱ : ℕ → String
  labelsⁱ = labels "In" (_++ "|")

  labelsᵒ : ℕ → String
  labelsᵒ = labels "Out" ("|" ++_)

  port : String → Id z → String
  port dir (mk comp port) = show comp ++ ":" ++ dir ++ show port

  wire : Id z → Id z → String
  wire src dst = port "Out" src ++ " -> " ++  port "In" dst

  comp : ℕ → Statement → List String
  comp comp# (mk op {i} ins o) with #atoms i | #atoms o
  ... | zero | zero = []  -- drop disconnected components
  ... | #i   | #j    =
    (show comp# ++
     " [label=\"" ++
     braces (labelsⁱ #i ++ op ++ labelsᵒ #j) ++
     "\"]")
    ∷ toList (zipWith (λ x i → wire x (mk comp# i)) ins indices)

dot : SSA a b → String
dot {a} (mk ss return) =
  (package ∘ concatᴸ ∘ mapℕ comp) (mk "In" · a ∷ ss ∷ʳ mk "Out" return ⊤)
