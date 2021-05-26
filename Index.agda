{-# OPTIONS --safe --without-K #-}

-- Indices of values within values

module Index where

open import Level
open import Data.Unit
open import Data.Sum hiding (map)
open import Data.Product using (_,_)
open import Function using (_∘_)

open import Categorical.Object
open import Categorical.Equiv
open import Ty
open import Functions.Type
open import Fun.Type
open import Fun.Raw

private variable a b z : Ty

data Index : Ty → Ty → Set where
  bit   : Index Bool Bool
  fun   : Index (a ⇛ b) (a ⇛ b)
  left  : Index z a → Index z (a × b)
  right : Index z b → Index z (a × b)

Indexer : Ty → Set
Indexer a = ∀ {z : Ty} → Index z a → Fₒ z

lookup : Fₒ a → Indexer a
lookup b          bit    = b
lookup f          fun    = f
lookup (x , _) (left  i) = lookup x i
lookup (_ , y) (right j) = lookup y j

tabulate : Indexer a → Fₒ a
tabulate {  `⊤  } f = tt
tabulate {`Bool } f = f bit
tabulate {_ `× _} f = tabulate (f ∘ left) , tabulate (f ∘ right)
tabulate {_ `⇛ _} f = f fun


open import Data.List

path : Index z a → List Bool
path bit       = []
path fun       = []
path (left  i) = 𝕗 ∷ path i
path (right j) = 𝕥 ∷ path j

open import Data.String hiding (show) renaming (_++_ to _++ᴸ_)

name : Index z a → String
name = fromList ∘ map (bool 'l' 'r') ∘ path

Indexed : (Ty → Set) → Ty → Set
Indexed h a = ∀ {z} → Index z a → h z

private variable h : Ty → Set

infixr 2 _,ᵢ_
_,ᵢ_ : Indexed h a → Indexed h b → Indexed h (a × b)
(f ,ᵢ g) (left  i) = f i
(f ,ᵢ g) (right j) = g j

exlᵢ : Indexed h (a × b) → Indexed h a
exlᵢ f = f ∘ left

exrᵢ : Indexed h (a × b) → Indexed h b
exrᵢ f = f ∘ right

splitᵢ : Indexed h (a × b) → Indexed h a × Indexed h b
splitᵢ f = exlᵢ f , exrᵢ f
-- splitᵢ f = f ∘ left , f ∘ right


open import Data.Bool using (if_then_else_)
open import Function using (id)
open import Show

show-indexed : ⦃ _ : ∀ {z : Ty} → Show (h z) ⦄ → Indexed h a → String
show-indexed {h = h} = go 𝕗 
 where
   -- Flag says we're in the left part of a pair
   go : Bool → Indexed h a → String
   go {a = `⊤} _ _ = "tt"
   go {a = `Bool} _ w = parensIfSpace (show (w bit))
   go {a = a `× b} p w = (if p then parens else id)
                         (go 𝕥 (exlᵢ w) ++ᴸ " , " ++ᴸ go 𝕗 (exrᵢ w))
   go {a = a `⇛ b} p w = parensIfSpace (show (w fun))

-- TODO: Consider turning Indexed into a data type, for pattern matching and
-- memoization. Then match on w instead of a in go, and eliminate _,ᵢ_, exlᵢ,
-- etc. Also, make show-indexed into an instance.

