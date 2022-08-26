open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟨_⟩)
open import Relation.Nullary

module Protocols.Ack-Based.Spec (Msg : Set)
                                (State : Set)
                                (step : State → Msg → State)
                                (gen-msgs : State → List (ℕ × Msg))
                                (_≟ₘ_ : (m₁ : Msg) → (m₂ : Msg) → Dec (m₁ ≡ m₂)) where



