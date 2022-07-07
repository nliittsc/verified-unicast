module Machine.ICoalgebra where

open import Machine.Core
open import Data.List
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Data.Unit
open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟨_⟩)

{--
  This file contains the transition system for the input buffer, written with a
  "coalgebra-style" semantics. The main invariants we want to maintain are:
    1. A "get" operation (receiving from the network) is always possible
    2. The input buffer only blocks if the main thread asks for a message, but
       the input buffer is empty.
--}

module IΔ (R S : Set) (sstep : S → Msg R → S) (produce : S → List (Msg R)) where

  open Δ R S sstep produce public
  Msg' = Msg R

  data Ack : Set where
    none : Ack
    ack-m : Ack

  data IAction : Set where
    get      : Msg' → IAction
    dlvr     : IAction

   -- The "input buffer functor". The type ⊤ indicates a "fault" or unallowed
  -- action.
  IB : Set → Set
  IB X = (IAction → ⊤ ⊎ (Ack × X))


  -- The state transition function of the input buffer. 
  δᵢ : Buffer Msg' → IB (Buffer Msg')
  δᵢ b (get m) = inj₂ (ack-m , enq m b)
  δᵢ (buffer [] s) dlvr                     = inj₂ (none , buffer [] blocking)
  δᵢ (buffer (m ∷ msgs) idle) dlvr          = inj₂ (none , buffer msgs transmit⟨ m ⟩)
  δᵢ (buffer (m ∷ msgs) blocking) dlvr      = inj₁ tt
  δᵢ (buffer (m ∷ msgs) transmit⟨ x ⟩) dlvr = inj₁ tt
