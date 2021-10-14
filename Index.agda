{-# OPTIONS --safe --without-K #-}

-- Indices of values within values

module Index where

open import Level
-- open import Data.Unit using (tt)
open import Data.Sum hiding (map)
open import Data.Product using (_,_; uncurry)
open import Function using (_∘_)

open import Categorical.Object
open import Categorical.Equiv
open import Ty
open import Functions.Type 0ℓ

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

Swizzle : Ty → Ty → Set  -- Rel Ty 0ℓ
Swizzle a b = ∀ {z} → Index z b → Index z a

swizzle : Swizzle a b → (Fₒ a → Fₒ b)
swizzle r x = tabulate (lookup x ∘ r)

open import Data.List renaming (map to mapᴸ) hiding (zip; zipWith)

infixr 4 _､_
data Indexed (h : Ty → Set) : Ty → Set where
  † : Indexed h ⊤
  [_]b : h Bool → Indexed h Bool
  [_]f : h (a ⇛ b) → Indexed h (a ⇛ b)
  _､_ : Indexed h a → Indexed h b → Indexed h (a × b)

private variable h : Ty → Set

lookup′ : Indexed h a → Indexer h a
lookup′ [ x ]b  bit       = x
lookup′ [ x ]f  fun       = x
lookup′ (u ､ v) (left  i) = lookup′ u i
lookup′ (u ､ v) (right i) = lookup′ v i

tabulate′ : ∀ {a h} → Indexer h a → Indexed h a
tabulate′ {  `⊤  } f = †
tabulate′ {`Bool } f = [ f bit ]b
tabulate′ {_ `⇛ _} f = [ f fun ]f
tabulate′ {_ `× _} f = tabulate′ (f ∘ left) ､ tabulate′ (f ∘ right)

swizzle′ : Swizzle a b → (Indexed h a → Indexed h b)
swizzle′ r a = tabulate′ (lookup′ a ∘ r)

-- TODO: Tabulate and indexed are very similar. Reconcile?

map : ∀ {h k} → (∀ {z} → h z → k z) → Indexed h a → Indexed k a
map g † = †
map g [ b ]b = [ g b ]b
map g [ f ]f = [ g f ]f
map g (u ､ v) = map g u ､ map g v

toList : ∀ {X} → Indexed (λ _ → X) a → List X
toList †       = []
toList [ b ]b  = [ b ]
toList [ f ]f  = [ f ]
toList (u ､ v) = toList u ++ toList v

indices : Indexed (λ z → Index z a) a
indices {  `⊤  } = †
indices {`Bool } = [ bit ]b
indices {a `⇛ b} = [ fun ]f
indices {a `× b} = map left indices ､ map right indices

zip : ∀ {h k} → Indexed h a → Indexed k a → Indexed (λ z → h z × k z) a
zip †        †        = †
zip [ x ]b  [ y ]b    = [ x , y ]b
zip [ x ]f  [ y ]f    = [ x , y ]f
zip (u ､ v) (u′ ､ v′) = zip u u′ ､ zip v v′

zipWith : ∀ {h k m} → (∀ {z} → h z → k z → m z) → Indexed h a → Indexed k a → Indexed m a
zipWith f u v = map (uncurry f) (zip u v)


module index-instances where
  instance
    open import Data.Bool as B using (if_then_else_)
    open import Data.Char using (Char)
    open import Function using (id)
    open import Show

    open import Data.String hiding (show) renaming (_++_ to _++ᴸ_)

    show-index : Show (Index z a)
    show-index = record { show = fromList ∘ mapᴸ name ∘ path }
     where
      name : B.Bool → Char
      name B.false = 'l'
      name B.true  = 'r'
      path : Index z a → List B.Bool
      path bit       = []
      path fun       = []
      path (left  i) = B.false ∷ path i
      path (right j) = B.true  ∷ path j

    show-indexed : ∀ {h} ⦃ _ : ∀ {z} → Show (h z) ⦄ → Show (Indexed h a)
    show-indexed {h = h} = record { show = go B.false }
     where
       -- Flag says we're in the left part of a pair
       go : B.Bool → Indexed h a → String
       go p † = "tt"
       go p [ b ]b = parensIfSpace (show b)
       go p [ f ]f = parensIfSpace (show f)
       go p (u ､ v) = (if p then parens else id) (go B.true u ++ᴸ " , " ++ᴸ go B.false v)
