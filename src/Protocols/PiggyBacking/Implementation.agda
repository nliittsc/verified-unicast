open import Data.Fin as F
open import Data.List
open import Data.List.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.Nat as ℕ
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟨_⟩)
open import Relation.Nullary
open import Relation.Unary
open ≡-Reasoning

module Protocols.PiggyBacking.Implementation (MsgRaw : Set)
                                             (num-site : ℕ)
                                             (_≡?_ : (mr₁ mr₂ : MsgRaw) → Dec (mr₁ ≡ mr₂)) where

import Protocols.Utils
open Protocols.Utils MsgRaw num-site _≡?_



