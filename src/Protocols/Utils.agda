open import Data.Fin as F
open import Data.Nat as ℕ
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟨_⟩)
open import Relation.Nullary

module Protocols.Utils (MsgRaw : Set)
                       (num-site : ℕ)
                       (_≡?_ : (mr₁ mr₂ : MsgRaw) → Dec (mr₁ ≡ mr₂)) where

Pid = Fin num-site

-- The message type. We assume decidability here
record Message : Set where
  constructor msg
  field
    sender  : Pid
    dest    : Pid
    payload : MsgRaw

-- open Message public


-- Total and Partial Maps
TotalMap : Set → Set → Set
TotalMap A B = A → B

map-update : ∀{A B : Set} → (_≟_ : (a₁ a₂ : A) → Dec (a₁ ≡ a₂)) →
             TotalMap A B → (key : A) → (val : B) → TotalMap A B
map-update _≟_ m k v k′ with k ≟ k′
... | yes p = v
... | no ¬p = m k′
