module Machine.Step where

open import Data.List
open import Data.List.Properties
open import Data.Product
open import Machine.Core
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟨_⟩)
open ≡-Reasoning

{- Setting up some neccesary abstractions here -}

BinRel : Set → Set → Set₁
BinRel A B = A → B → Set

Relation : Set → Set₁
Relation A = BinRel A A

TriRel : Set → Set → Set → Set₁
TriRel A B C = A → B → C → Set

LabeledRel : Set → Set → Set₁
LabeledRel A B = TriRel A B A


---------- Unlabled Transition Relation ----------


-- Define the abstract multi-step (unlabled) transition relation
data multi {X : Set} (R : Relation X) : Relation X where
  multi-refl : ∀ (x : X) → multi R x x
  multi-step : ∀ (x y z : X) → R x y → multi R y z → multi R x z

-- We can replace a single step with a "multi"-step
one-step-thm : ∀{X : Set} (R : Relation X) (x y : X) → R x y → (multi R) x y
one-step-thm R x y Rxy = multi-step x y y Rxy (multi-refl y)

-- the mult-step relation is transitive
multi-trans : ∀{X : Set} (R : Relation X) (x y z : X) → multi R x y → multi R y z → multi R x z
multi-trans R x .x z (multi-refl .x) R⋆yz = R⋆yz
multi-trans R x y₁ z (multi-step .x y .y₁ Rxy R⋆yy₁) R⋆yz = multi-step x y z Rxy (multi-trans R y y₁ z R⋆yy₁ R⋆yz)


---------- Labeled Transition Relation ----------



{- Define the abstract multi-step (labeled) transition relation.
   Sequences of actions are contained in lists -}
data labeled-multi {X A : Set} (R : LabeledRel X A) : LabeledRel X (List A) where
  multi-refl : ∀(x : X) → labeled-multi R x [] x
  multi-step : ∀(x y z : X) (α : A) (ω : List A) → R x α y → labeled-multi R y ω z →
               labeled-multi R x (α ∷ ω) z

-- Analagous to `one-step-thm` but with sequences
labeled-one-step-thm : ∀{X A : Set} (R : LabeledRel X A) (x y : X) (α : A) →
                       R x α y → labeled-multi R x [ α ] y
labeled-one-step-thm R x y α Rxαy = multi-step x y y α [] Rxαy (multi-refl y)


-- Not sure if needed...
labeled-multi-refl-lemma : ∀{X A : Set} (R : LabeledRel X A) (x y : X) (ω : List A) →
                          labeled-multi R x ω y → labeled-multi R x (ω ++ []) y
labeled-multi-refl-lemma R x y ω R⋆xωy = subst (λ l → labeled-multi R x l y) (sym (++-identityʳ ω)) R⋆xωy


-- Analagous to `multi-trans`, but with labeled sequences
labeled-multi-trans : ∀{X A : Set} (R : LabeledRel X A) (x y z : X) (ω₁ ω₂ : List A) →
                      labeled-multi R x ω₁ y → labeled-multi R y ω₂ z → labeled-multi R x (ω₁ ++ ω₂) z
labeled-multi-trans R x .x z .[] ω₂ (multi-refl .x) R⋆yω₂z = R⋆yω₂z
labeled-multi-trans R x y z .(α ∷ ω) ω₂ (multi-step .x y₁ .y α ω x₁ R⋆xω₁y) R⋆yω₂z = proof
  where
    proof : labeled-multi R x (α ∷ ω ++ ω₂) z
    proof = let ind-step = (labeled-multi-trans R y₁ y z ω ω₂ R⋆xω₁y R⋆yω₂z)
            in  multi-step x y₁ z α (ω ++ ω₂) x₁ ind-step


{- TRANSITION STATES -}

-- The generalized local state of a process
record LState (A S : Set) : Set₁ where
  constructor ⟨_,_⟩
  field
    history : List (Msg A)
    state   : S
