module CoAlgebra where

open import Data.Product
open import Data.Sum
open import Function
open import Data.List hiding ([_])
open import Relation.Binary.PropositionalEquality


-- The proposition that F is a functor
record IsFunctor (F : Set → Set) : Set₁ where
  field
    fmap    : ∀ {A B} → (A → B) → F A → F B

    fmap-id : ∀ {A} (fx : F A) → fmap id fx ≡ id fx

    fmap-∘  : ∀ {A B C} {f : A → B} {g : B → C}
              (fx : F A) → fmap (g ∘ f) fx ≡ ((fmap g) ∘ (fmap f)) fx

open IsFunctor public

-- The proposition that we have a Coalgebra. α is a morphism
record IsCoalgebra (A : Set) (F : Set → Set) (α : A → F A) : Set₁ where
  constructor CoA
  field
    isFunctor : IsFunctor F


-- The type of functors
record Functor : Set₁ where
  field
    𝑭 : Set → Set
    isFunctor : IsFunctor 𝑭

open Functor public

-- The type of F-Coalgebras
record Coalgebra : Set₁ where
  field
    Carrier : Set
    functor : Functor
    morphism : Carrier → (𝑭 functor) Carrier


open Functor public
open Coalgebra public




