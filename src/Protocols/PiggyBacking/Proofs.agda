open import Data.Fin as F
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.Nat as ℕ
open import Data.Product
open import Data.Sum
open import Data.Vec as V hiding (_++_; [_]) renaming (lookup to lkup)
open import Data.Vec.Properties
open import Function
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟨_⟩)
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Unary renaming (_∈_ to _∈ₚ_; _⊆_ to _⊆ₚ_)

open ≡-Reasoning
open import Abstractions.Coalgebra

module Protocols.PiggyBacking.Proofs (MsgRaw : Set)
                                     (num-site : ℕ)
                                     (_≡?_ : (mr₁ mr₂ : MsgRaw) → Dec (mr₁ ≡ mr₂))
                                     (LocalState : Set)
                                     (initState : LocalState)
                                     (step : LocalState → MsgRaw → LocalState)
                                     (produce : LocalState → Fin num-site × MsgRaw) where

import Protocols.PiggyBacking.Implementation
import Protocols.Utils
open Protocols.Utils MsgRaw num-site _≡?_
open Protocols.PiggyBacking.Implementation MsgRaw num-site _≡?_


data Event : Set where
  send : Message → Event
  dlvr : Message → Event


Packet = Message × List Event
History = List Event
-- The channel chanᵢⱼ are unreceived messages from i to j
Channel = Vec (Vec (List Packet) num-site) num-site
State = Vec (LocalState × History) num-site

Config = Channel × State

stamp : Config → Message → Packet
stamp (chan , s) m = m , h
  where
    h : List Event
    h = proj₂ (lkup s (sender m))

send-step : Config → Message → Config
send-step c m = {!!}

-- List ordering. `a` comes before `b` in list `xs`.
_≺[_]_ : ∀{A : Set} → A → List A → A → Set
a ≺[ xs ] b = ∃₂ λ ys zs → (xs ≡ ys ++ zs × a ∈ ys × b ∈ zs)

