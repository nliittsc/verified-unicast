open import Data.List

module Abstractions.Coalgebra where

data multi {S A : Set} (step : S → A → S → Set) : S → List A → S → Set where
  step-refl : ∀ s → multi step s [] s
  step-iter : ∀ s s′ s″ ω a → step s a s′ → multi step s′ ω s″ →
              multi step s (a ∷ ω) s″
