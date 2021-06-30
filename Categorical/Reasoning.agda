{-# OPTIONS --safe --without-K #-}

-- Utilities for reasoning about morphism equivalence.

-- Inspired by Categories.Morphism.Reasoning in agda-categories. Quoting that
-- module:

{-
  Helper routines most often used in reasoning with commutative squares,
  at the level of arrows in categories.

  Basic  : reasoning about identity
  Pulls  : use a ∘ b ≈ c as left-to-right rewrite
  Pushes : use c ≈ a ∘ b as a left-to-right rewrite
  IntroElim : introduce/eliminate an equivalent-to-id arrow
  Extend : 'extends' a commutative square with an equality on left/right/both
-}

open import Categorical.Equiv
open import Categorical.Raw
open import Categorical.Laws as L
       hiding (Category; Cartesian; CartesianClosed)

module Categorical.Reasoning
    {o}{obj : Set o} {ℓ} {_⇨_ : obj → obj → Set ℓ} ⦃ _ : Category _⇨_ ⦄
    {q} ⦃ _ : Equivalent q _⇨_ ⦄ ⦃ _ : L.Category _⇨_ ⦄
  where

open import Level
open import Function using (_∘′_)

private
  variable
    a b c d e : obj
    a′ b′ c′ d′ e′ : obj
    f g h i j k : a ⇨ b

open import Categorical.Equiv  public
open ≈-Reasoning

module Misc where

  sym-sym : {i j : a ⇨ b} {f g : c ⇨ d} → (i ≈ j → f ≈ g) → (j ≈ i → g ≈ f)
  sym-sym f≈g = sym ∘′ f≈g ∘′ sym
  -- sym-sym f≈g i≈j = sym (f≈g (sym i≈j))

  -- I've been able to use sym-sym, due to implicits

open Misc public


module Pulls {i : b ⇨ c}{j : c ⇨ d}{k : b ⇨ d} (j∘i≈k : j ∘ i ≈ k) where

  pullˡ : {f : a ⇨ b} → j ∘ i ∘ f ≈ k ∘ f
  pullˡ {f = f} = begin
                    j ∘ (i ∘ f)
                  ≈⟨ ∘-assocˡ ⟩
                    (j ∘ i) ∘ f
                  ≈⟨ ∘≈ˡ j∘i≈k ⟩
                    k ∘ f
                  ∎

  pullʳ : {f : d ⇨ e} → (f ∘ j) ∘ i ≈ f ∘ k
  pullʳ {f = f} = begin
                    (f ∘ j) ∘ i
                  ≈⟨ ∘-assocʳ ⟩
                    f ∘ (j ∘ i)
                  ≈⟨ ∘≈ʳ j∘i≈k ⟩
                    f ∘ k
                  ∎

open Pulls public


module Pushes {i : b ⇨ c}{j : c ⇨ d}{k : b ⇨ d} (k≈j∘i : k ≈ j ∘ i) where

  private j∘i≈k = sym k≈j∘i

  pushˡ : {f : a ⇨ b} → k ∘ f ≈ j ∘ i ∘ f
  pushˡ = sym (pullˡ j∘i≈k)

  pushʳ : {f : d ⇨ e} → f ∘ k ≈ (f ∘ j) ∘ i
  pushʳ = sym (pullʳ j∘i≈k)

open Pushes public


module IntroElim {i : b ⇨ b} (i≈id : i ≈ id) where

  elimˡ  : ∀ {f : a ⇨ b} → i ∘ f ≈ f
  elimˡ  {f = f} = begin
                     i ∘ f
                   ≈⟨ ∘≈ˡ i≈id ⟩
                     id ∘ f
                   ≈⟨ identityˡ ⟩
                     f
                   ∎

  introˡ : ∀ {f : a ⇨ b} → f ≈ i ∘ f
  introˡ = sym elimˡ

  elimʳ  : ∀ {f : b ⇨ c} → f ∘ i ≈ f
  elimʳ  {f = f} = begin
                     f ∘ i
                   ≈⟨ ∘≈ʳ i≈id ⟩
                     f ∘ id
                   ≈⟨ identityʳ ⟩
                     f
                   ∎

  introʳ : ∀ {f : b ⇨ c} → f ≈ f ∘ i
  introʳ = sym elimʳ

  intro-center : ∀ {f : a ⇨ b} {g : b ⇨ c} → g ∘ f ≈ g ∘ i ∘ f
  intro-center = ∘≈ʳ introˡ

  elim-center  : ∀ {f : a ⇨ b} {g : b ⇨ c} → g ∘ i ∘ f ≈ g ∘ f
  elim-center  = sym intro-center

open IntroElim public


module Assoc where

  -- TODO: Maybe move ∘-assocˡ′ and ∘-assocʳ′ to Pulls

  ∘-assocˡ′ : ∀ {f : a ⇨ b}{g : b ⇨ c}{h : c ⇨ d}{k : b ⇨ d}
            → h ∘ g ≈ k → h ∘ (g ∘ f) ≈ k ∘ f
  ∘-assocˡ′ h∘g≈k = ∘-assocˡ ; ∘≈ˡ h∘g≈k

  ∘-assocʳ′ : ∀ {f : a ⇨ b}{g : b ⇨ c}{h : a ⇨ c}{k : c ⇨ d}
            → g ∘ f ≈ h → (k ∘ g) ∘ f ≈ k ∘ h
  ∘-assocʳ′ g∘f≈h = ∘-assocʳ ; ∘≈ʳ g∘f≈h


  ∘-assocˡʳ′ : ∀ {f : a ⇨ b}{g : b ⇨ c}{h : c ⇨ d}{i : b ⇨ c′}{j : c′ ⇨ d}
             → h ∘ g ≈ j ∘ i → h ∘ (g ∘ f) ≈ j ∘ (i ∘ f)
  ∘-assocˡʳ′ h∘g≈j∘i = ∘-assocˡ′ h∘g≈j∘i ; ∘-assocʳ

  ∘-assocʳˡ′ : ∀ {f : a ⇨ b}{g : b ⇨ c}{h : c ⇨ d}{i : a ⇨ b′}{j : b′ ⇨ c}
             → g ∘ f ≈ j ∘ i → (h ∘ g) ∘ f ≈ (h ∘ j) ∘ i
  ∘-assocʳˡ′ g∘f≈j∘i = ∘-assocʳ′ g∘f≈j∘i ; ∘-assocˡ


  ∘-assoc-elimˡ : ∀ {f : a ⇨ b}{i : b ⇨ c}{j : c ⇨ b}
                → j ∘ i ≈ id → j ∘ (i ∘ f) ≈ f
  ∘-assoc-elimˡ {f = f}{i}{j} j∘i≈id = ∘-assocˡ ; elimˡ j∘i≈id

  ∘-assoc-elimʳ : ∀ {i : a ⇨ b}{j : b ⇨ a}{f : a ⇨ c}
                → j ∘ i ≈ id → (f ∘ j) ∘ i ≈ f
  ∘-assoc-elimʳ {i = i}{f}{j} j∘i≈id = ∘-assocʳ ; elimʳ j∘i≈id

open Assoc public
