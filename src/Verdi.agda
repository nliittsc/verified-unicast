module Verdi where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product
open import Data.List
open import Data.List.Relation.Binary.Permutation.Propositional renaming (_↭_ to Permute)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

record Packet (Node Msg : Set) : Set where
  constructor _⇒_⦂_
  field
    src : Node
    dst : Node
    msg : Msg

record App : Set₁ where
  field
    Node   : Set
    _≟_    : (n : Node) → (m : Node) → Dec (n ≡ m)
    State  : Node → Set
    Msg    : Set
    Input  : Set
    Output : Set
    initState : (n : Node) → State n
    HandleInp : (n : Node) → State n → Input → (State n × Output × List (Packet Node Msg))
    HandleMsg : (n : Node) → State n → Packet Node Msg → (State n × Output × List (Packet Node Msg))

module _ (app : App) where
  open App app
  open Packet

  Event = Node × (Input ⊎ Output)
  Trace = List Event
  NodeStates = (n : Node) → State n
  Packets = List (Packet Node Msg)

  World = Packets × NodeStates × Trace

  _[_↦_] : NodeStates → (n : Node) → State n → NodeStates
  _[_↦_] S n s n′ with n ≟ n′
  ... | yes refl = s
  ... | no  _    = S n′

  data _==>ᵣ_ : World → World → Set where
    input : ∀ P Σ T n i σ′ o P′ Σ′ →
            HandleInp n (Σ n) i ≡ (σ′ , o , P′) →
            Σ′ ≡ Σ [ n ↦ σ′ ] →
            (P , Σ , T) ==>ᵣ (P ++ P′ , Σ′ , T ++ (n , inj₁ i) ∷ (n , inj₂ o) ∷ [])
    deliver : ∀ p P σ′ o P′ T Σ′ n Σ →
              HandleMsg (dst p) (Σ (dst p)) p ≡ (σ′ , o , P′) →
              Σ′ ≡ Σ [ dst p ↦ σ′ ] →
              (p ∷ P , Σ , T) ==>ᵣ (P ++ P′ , Σ′ , T ++ (n , inj₂ o) ∷ [])
    permute : ∀ P Σ T P′ →
              Permute P P′ →
             (P , Σ , T) ==>ᵣ (P′ , Σ , T)
