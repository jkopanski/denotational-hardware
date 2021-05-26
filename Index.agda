{-# OPTIONS --safe --without-K #-}

-- Indices of values within values

module Index where

open import Level
open import Data.Unit using (tt)
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

Indexer : (Ty → Set) → Ty → Set
Indexer h a = ∀ {z : Ty} → Index z a → h z

lookup : Fₒ a → Indexer Fₒ a
lookup b          bit    = b
lookup f          fun    = f
lookup (x , _) (left  i) = lookup x i
lookup (_ , y) (right j) = lookup y j

tabulate : Indexer Fₒ a → Fₒ a
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

infixr 4 _､_
data Indexed (h : Ty → Set) : Ty → Set where
  · : Indexed h ⊤
  [_]b : h Bool → Indexed h Bool
  _､_ : Indexed h a → Indexed h b → Indexed h (a × b)
  [_]f : h (a ⇛ b) → Indexed h (a ⇛ b)

private variable h : Ty → Set

lookup′ : Indexed h a → Indexer h a
lookup′ [ x ]b   bit      = x
lookup′ (u ､ v) (left  i) = lookup′ u i
lookup′ (u ､ v) (right i) = lookup′ v i
lookup′ [ f ]f  fun       = f

tabulate′ : ∀ {a h} → Indexer h a → Indexed h a
tabulate′ {  `⊤  } f = ·
tabulate′ {`Bool } f = [ f bit ]b
tabulate′ {_ `× _} f = tabulate′ (f ∘ left) ､ tabulate′ (f ∘ right)
tabulate′ {_ `⇛ _} f = [ f fun ]f

swizzle′ : (∀ {z} → Index z b → Index z a) → (Indexed h a → Indexed h b)
swizzle′ r a = tabulate′ (lookup′ a ∘ r)

-- TODO: Tabulate and indexed are very similar. Reconcile?

module index-instances where
  instance
    open import Data.Bool using (if_then_else_)
    open import Function using (id)
    open import Show
     
    show-indexed : ∀ {h} ⦃ _ : ∀ {z} → Show (h z) ⦄ → Show (Indexed h a)
    show-indexed {h = h} = record { show = go 𝕗 }
     where
       -- Flag says we're in the left part of a pair
       go : Bool → Indexed h a → String
       go p · = "tt"
       go p [ b ]b = parensIfSpace (show b)
       go p (u ､ v) = (if p then parens else id) (go 𝕥 u ++ᴸ " , " ++ᴸ go 𝕗 v)
       go p [ f ]f = parensIfSpace (show f)
