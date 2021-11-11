module StronglyFinite where

-- Full subcategory of Function restricted to finite sets.

-- TODO: Try generalizing from functions to any category with sets as objects.

-- https://github.com/conal/denotational-hardware/commit/9472458b7611c44a41069345721d58f51478c430#commitcomment-59932515
-- from Jacques Carette: "These are 'strongly finite' sets, in the sense that
-- not only is the n visible, but which proof of isomorphism is also visible.
-- The properties of finite sets should, in theory, never depend on the exact
-- proof. This is why Brent needed to go to HoTT in his thesis, and also why
-- trying to do Species-like things in Haskell is hard (it's hard to hide that
-- isomorphism choice)."

open import Level using (0ℓ)
open import Function using (_↔_; mk↔′; Inverse) renaming (_∘_ to _∘′_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Nat
open import Data.Fin renaming (Fin to 𝔽)
open import Data.Fin.Properties
open import Data.Fin.Patterns using (0F; 1F)
open import Relation.Binary.PropositionalEquality using (refl)

open import Categorical.Homomorphism hiding (refl) renaming (Bool to 𝔹)
open import Categorical.Laws
open import Functions 0ℓ

open import Finite renaming (_⇨_ to _↠_; mk to mk↠; un to un↠)

-- A finite set, demonstrated by a number n and proof that A ≅ 𝔽 n.
record StronglyFinite : Set₁ where
  constructor mkO
  field
    { A } : Set
    { n } : ℕ
    iso : A ↔ 𝔽 n

private

    -- Like mk↔′ but for matching
    pattern mk↔ f f⁻¹ f∘f⁻¹ f⁻¹∘f =
      record { f = f ; f⁻¹ = f⁻¹ ; inverse = f∘f⁻¹ , f⁻¹∘f }

module StronglyFinite-Set-instances where

  instance

    open import Categorical.Reasoning

    Hₒ : Homomorphismₒ StronglyFinite Set
    Hₒ = record { Fₒ = StronglyFinite.A }

    products : Products StronglyFinite
    products = record
      { ⊤ = mkO (mk↔′ ε ε⁻¹ ε∘ε⁻¹ ε⁻¹∘ε)
      ; _×_ = λ (mkO {A} {m} (mk↔ f f⁻¹ f∘f⁻¹ f⁻¹∘f))
                (mkO {B} {n} (mk↔ g g⁻¹ g∘g⁻¹ g⁻¹∘g)) →
                let open ≈-Reasoning in
         mkO {A × B} {m × n}
           (mk↔′ (μ ∘ (f ⊗ g)) ((f⁻¹ ⊗ g⁻¹) ∘ μ⁻¹)
             (begin
                (μ ∘ (f ⊗ g)) ∘ ((f⁻¹ ⊗ g⁻¹) ∘ μ⁻¹)
              ≈⟨ cancelInner
                   {i = f⁻¹ ⊗ g⁻¹} {h = f ⊗ g}
                   (⊗-inverse {f = f⁻¹} {f} {g⁻¹} {g} f∘f⁻¹ g∘g⁻¹)
                   {f = μ} {g = μ⁻¹} ⟩
                 μ ∘ μ⁻¹ {a = m}
              ≈⟨ μ∘μ⁻¹ {a = m} ⟩
                id
              ∎)
             (begin
                ((f⁻¹ ⊗ g⁻¹) ∘ μ⁻¹) ∘ (μ ∘ (f ⊗ g))
              ≈⟨ cancelInner {i = μ} {h = μ⁻¹} μ⁻¹∘μ {f = f⁻¹ ⊗ g⁻¹} {g = f ⊗ g} ⟩
                 (f⁻¹ ⊗ g⁻¹) ∘ (f ⊗ g)
              ≈⟨ (⊗-inverse {f = f} {f⁻¹} {g} {g⁻¹} f⁻¹∘f g⁻¹∘g) ⟩
                id
              ∎)
           )  -- TODO: simplify with a monoidal category of isomorphisms.
      }

    productsH : ProductsH StronglyFinite ⟨→⟩
    productsH = record { ε     = id
                       ; μ     = id
                       ; ε⁻¹   = id
                       ; μ⁻¹   = id
                       ; ε⁻¹∘ε = λ _ → refl
                       ; ε∘ε⁻¹ = λ _ → refl
                       ; μ⁻¹∘μ = λ _ → refl
                       ; μ∘μ⁻¹ = λ _ → refl
                       }

    -- TODO: Coproducts
    -- TODO: Exponentials

    boolean : Boolean StronglyFinite
    boolean = record { Bool = mkO (mk↔′ β β⁻¹ β∘β⁻¹ β⁻¹∘β) }

    booleanH : BooleanH StronglyFinite ⟨→⟩
    booleanH = record { β = id ; β⁻¹ = id }

    strongBooleanH : StrongBooleanH StronglyFinite ⟨→⟩
    strongBooleanH = record { β⁻¹∘β = λ _ → refl ; β∘β⁻¹ = λ _ → refl }

-- Define the subcategory of ⟨→⟩ with homomorphisms and laws
open import Categorical.Subcategory ⟨→⟩ StronglyFinite
      renaming (mk to mk⇨) -- TEMP
      public

module StronglyFinite-ℕ-instances where

  instance

    Hₒ : Homomorphismₒ StronglyFinite ℕ
    Hₒ = record { Fₒ = StronglyFinite.n }

    productsH : ProductsH StronglyFinite _↠_
    productsH = record
               { ε     = id
               ; μ     = id
               ; ε⁻¹   = id
               ; μ⁻¹   = id
               ; ε⁻¹∘ε = λ _ → refl
               ; ε∘ε⁻¹ = λ _ → refl
               ; μ⁻¹∘μ = λ _ → refl
               ; μ∘μ⁻¹ = λ _ → refl
               }

    -- TODO: Coproducts
    -- TODO: Exponentials

    booleanH : BooleanH StronglyFinite _↠_
    booleanH = record { β = id ; β⁻¹ = id }

    strongBooleanH : StrongBooleanH StronglyFinite _↠_
    strongBooleanH = record { β⁻¹∘β = λ _ → refl ; β∘β⁻¹ = λ _ → refl }

    H : Homomorphism _⇨_ _↠_
    H = record
      { Fₘ = λ { {mkO (mk↔ _ fin₁⁻¹ _ _)} {mkO (mk↔ fin₂ _ _ _)} (mk⇨ g) →
               mk↠ (fin₂ ∘ g ∘ fin₁⁻¹) } }

    categoryH : CategoryH _⇨_ _↠_
    categoryH = record
      { F-id = λ { {mkO {A} {n} (mk↔ fin fin⁻¹ fin∘fin⁻¹ _)} x →
                   begin
                     fin (id (fin⁻¹ x))
                   ≡⟨⟩
                     fin (fin⁻¹ x)
                   ≡⟨ fin∘fin⁻¹ x ⟩
                     x
                   ∎
                 }
      ; F-∘ = λ { {mkO (mk↔ fin₁ fin⁻¹₁ fin∘fin⁻¹₁ fin⁻¹∘fin₁)}
                  {mkO (mk↔ fin₂ fin⁻¹₂ fin∘fin⁻¹₂ fin⁻¹∘fin₂)}
                  {mkO (mk↔ fin₃ fin⁻¹₃ fin∘fin⁻¹₃ fin⁻¹∘fin₃)}
                  {mk⇨ g} {mk⇨ f} x →
                  begin
                    fin₃ (g (f (fin⁻¹₁ x)))
                  ≡˘⟨ cong (fin₃ ∘ g) (fin⁻¹∘fin₂ (f (fin⁻¹₁ x))) ⟩
                    fin₃ (g (fin⁻¹₂ (fin₂ (f (fin⁻¹₁ x)))))
                  ∎
                }
      } where open import Relation.Binary.PropositionalEquality
              open ≡-Reasoning

    cartesianH : CartesianH _⇨_ _↠_
    cartesianH = record
      { F-! = λ _ → refl
      ; F-▵ = λ _ → refl
      ; F-exl = λ { {mkO {A} {m} (mk↔ fin₁ fin⁻¹₁ fin∘fin⁻¹₁ fin⁻¹∘fin₁)}
                    {mkO {B} {n} (mk↔ fin₂ fin⁻¹₂ fin∘fin⁻¹₂ fin⁻¹∘fin₂)} x →
                    fin∘fin⁻¹₁ (exl (μ⁻¹ x))
                  }
      ; F-exr = λ { {mkO {A} {m} (mk↔ fin₁ fin⁻¹₁ fin∘fin⁻¹₁ fin⁻¹∘fin₁)}
                    {mkO {B} {n} (mk↔ fin₂ fin⁻¹₂ fin∘fin⁻¹₂ fin⁻¹∘fin₂)} x →
                    fin∘fin⁻¹₂ (exr (μ⁻¹ {a = m} x))
                  }
      } where open ≈-Reasoning
              -- open import Relation.Binary.PropositionalEquality
              -- open ≡-Reasoning

    -- Note the laws:
    -- 
    --   F-exl : ∀ {a b : obj₁} → Fₘ exl ∘ μ {a = a}{b} ≈ exl
    --   F-exr : ∀ {a b : obj₁} → Fₘ exr ∘ μ {a = a}{b} ≈ exr
    --
    -- TODO: rephrase as Fₘ exl ≈ exl ∘ μ⁻¹ {a = a}{b} and likewise for F-exr
    -- (currently F-exl′ and F-exr′). Then the proofs above probably go through
    -- as λ _ → refl, as with F-! and F-▵. I suspect many other proofs become
    -- easier as well.

    -- TODO: prove these laws in general when 

    logicH : LogicH _⇨_ _↠_
    logicH = record
      { F-false = λ _ → refl
      ; F-true  = λ _ → refl
      ; F-not   = λ _ → refl
      ; F-∧     = cong (un↠  ∧ ) ∘′ μ∘μ⁻¹ {a = 2} {2}
      ; F-∨     = cong (un↠  ∨ ) ∘′ μ∘μ⁻¹ {a = 2} {2}
      ; F-xor   = cong (un↠ xor) ∘′ μ∘μ⁻¹ {a = 2} {2}

      ; F-cond  = λ { a@{mkO {A} {n} (mk↔ fin fin⁻¹ fin∘fin⁻¹ fin⁻¹∘fin)} x →
          let Fₘ-cond₁ : 𝔹 × n × n ↠ n
              Fₘ-cond₁ = Fₘ {_⇨₁_ = _⇨_} {_⇨₂_ = _↠_} (cond {_⇨′_ = _⇨_} {a = a})
              cond→ : {t : Set} → 𝔹 × t × t → t
              cond→ = cond
              fin⁻¹-𝔹×a×a = Inverse.f⁻¹ (StronglyFinite.iso (𝔹 × a × a))
              fin⁻¹-a×a = Inverse.f⁻¹ (StronglyFinite.iso (a × a))
              Fₘ-cond₂ : 𝔹 × n × n ↠ n
              Fₘ-cond₂ = Fₘ {_⇨₁_ = _⇨_} {_⇨₂_ = _↠_} {a = 𝔹 × a × a} {b = a}
                (mk⇨ (cond ∘ (β⁻¹ ⊗ μ⁻¹ {a = a}{a}) ∘ μ⁻¹ {a = 𝔹}{a × a}))
              Fₘ-cond₃ : 𝔹 × n × n ↠ n
              Fₘ-cond₃ =
                mk↠ ( fin
                    ∘ (cond ∘ (β⁻¹ ⊗ μ⁻¹ {a = a}{a}) ∘ μ⁻¹ {a = 𝔹}{a × a})
                    ∘ fin⁻¹-𝔹×a×a )
              c , pq = μ𝔽⁻¹ {𝔹} {n × n} x
              p , q = μ𝔽⁻¹ {n} {n} pq
          in
          begin
            un↠ (Fₘ (cond {a = a}) ∘ μ {a = 𝔹} {b = a × a} ∘ (β ⊗ μ {a = a} {a})) x
          ≡⟨⟩
            un↠ (Fₘ (cond {a = a}) ∘ (β ⊗ μ {a = a} {a})) x
          ≡⟨⟩
            un↠ (Fₘ (cond {a = a})) ((un↠ (β ⊗ μ {a = a} {a})) x)
          ≡⟨ cong (un↠ (Fₘ (cond {a = a}))) (μ∘μ⁻¹ {a = 2} {n × n} x) ⟩
            un↠ (Fₘ (cond {a = a})) x
          ≡⟨⟩
            un↠ Fₘ-cond₁ x
          ≡⟨⟩
            un↠ Fₘ-cond₂ x
          ≡⟨⟩
            un↠ Fₘ-cond₃ x
          ≡⟨⟩
            (fin ∘ (cond→ ∘ (β⁻¹ ⊗ μ⁻¹ {a = a}{a}) ∘ μ⁻¹ {a = 𝔹}{a × a}) ∘ fin⁻¹-𝔹×a×a) x
          ≡⟨⟩
            fin (cond→ ((β⁻¹ ⊗ μ⁻¹ {a = a}{a}) (μ⁻¹ {a = 𝔹}{a × a} (fin⁻¹-𝔹×a×a x))))
          ≡⟨ f∘cond→ {f = fin} _ ⟩
            cond→ ((β⁻¹ ⊗ (fin ⊗ fin) ∘ μ⁻¹ {a = a}{a}) (μ⁻¹ {a = 𝔹}{a × a} (fin⁻¹-𝔹×a×a x)))
          ≡⟨⟩
            cond→ ((β⁻¹ ⊗ (fin ⊗ fin) ∘ μ⁻¹ {a = a}{a}) (μ⁻¹ {a = 𝔹}{a × a} ((β⁻¹ ⊗ fin⁻¹-a×a) (μ⁻¹ x))))
          ≡⟨⟩
            cond→ ((β⁻¹ ⊗ (fin ⊗ fin) ∘ μ⁻¹ {a = a}{a}) (μ⁻¹ {a = 𝔹}{a × a} ((β⁻¹ ⊗ ((fin⁻¹ ⊗ fin⁻¹) ∘ μ⁻¹)) (μ⁻¹ x))))
          ≡⟨⟩
            cond→ ((β⁻¹ ⊗ (fin ⊗ fin) ∘ μ⁻¹ {a = a}{a}) (μ⁻¹ {a = 𝔹}{a × a} ((β⁻¹ ⊗ ((fin⁻¹ ⊗ fin⁻¹) ∘ μ⁻¹)) (c , pq))))
          ≡⟨⟩
            cond→ ((β⁻¹ ⊗ (fin ⊗ fin) ∘ μ⁻¹ {a = a}{a}) (μ⁻¹ {a = 𝔹}{a × a} (β⁻¹ c , ((fin⁻¹ ⊗ fin⁻¹) ∘ μ⁻¹) pq)))
          ≡⟨⟩
            cond→ ((β⁻¹ ⊗ (fin ⊗ fin) ∘ μ⁻¹ {a = a}{a}) (μ⁻¹ {a = 𝔹}{a × a} (β⁻¹ c , fin⁻¹ p , fin⁻¹ q)))
          ≡⟨⟩
            cond→ ((id ⊗ (fin ⊗ fin)) (β⁻¹ c , fin⁻¹ p , fin⁻¹ q))
          ≡⟨⟩
            cond→ (β⁻¹ c , fin (fin⁻¹ p) , fin (fin⁻¹ q))
          ≡⟨ cong₂ (λ ○ ● → cond→ (β⁻¹ c , ○ , ●)) (fin∘fin⁻¹ p) (fin∘fin⁻¹ q) ⟩
            cond→ (β⁻¹ c , p , q)
          ≡⟨⟩
            cond→ (β⁻¹ c , μ⁻¹ pq)
          ≡⟨⟩
            cond→ ((β⁻¹ ⊗ μ⁻¹) (c , pq))
          ≡⟨⟩
            (cond→ ∘ (β⁻¹ ⊗ μ⁻¹) ∘ μ⁻¹) x
          ≡⟨⟩
            un↠ (mk↠ (cond→ ∘ (β⁻¹ ⊗ μ⁻¹) ∘ μ⁻¹)) x
          ≡⟨⟩
            un↠ cond x
          ∎
          }

          -- TODO: simplify this proof enormously! For one thing, keep the outer
          -- fin outside, and move the pair of fins out via cond→.

{-
      ; F-∧     = λ (x : 𝔽 (2 × 2)) →
          -- ∧ = mk (β ∘ ∧ ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹)
          -- F-∧ : Fₘ ∧ ∘ μ ∘ (β ⊗ β) ≈ β ∘ ∧
          begin
            un↠ (Fₘ ∧ ∘ μ {a = 𝔹}{𝔹} ∘ (β ⊗ β)) x
          ≡⟨⟩
            un↠ ∧ (μ𝔽 (μ𝔽⁻¹ x))
          ≡⟨ cong (un↠ ∧) (μ𝔽∘μ𝔽⁻¹ x) ⟩
            un↠ (Fₘ ∧) x
          ≡⟨⟩
            un↠ ∧ x
          ∎
-}

      } where -- open import Data.Bool using () renaming (Bool to B)
              -- open ≈-Reasoning
              -- open import Categorical.Reasoning
              open import Relation.Binary.PropositionalEquality
              open ≡-Reasoning

              μ𝔽 : {m n : ℕ} → 𝔽 m × 𝔽 n → 𝔽 (m × n)
              μ𝔽 = μ
              μ𝔽⁻¹ : {m n : ℕ} → 𝔽 (m × n) → 𝔽 m × 𝔽 n
              μ𝔽⁻¹ = μ⁻¹



-- We could now define a subcategory of Finite.

