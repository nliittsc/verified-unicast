module Machine.OCoalgebra where

open import Machine.Core
open import Data.List
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Data.Unit
open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟨_⟩)


{-- This file contains the Coalgebra Semantics for the Output Buffer.
    The main invariants we want to maintain are:
      1. Inserting is always possible
      2. Any successful, asynchronous post is followed by a block until an
         acknowledgement is received
      3. If the buffer is empty, then it idles. When non-empty, it either
         has a message ready to post, or is waiting for an ack.
--}


module OΔ (R S : Set) (sstep : S → Msg R → S) (produce : S → List (Msg R)) where

  open Δ R S sstep produce public
  Msg' = Msg R
  
  -- The input actions of the output buffer --
  data OAction : Set where
    insert : Msg' → OAction
    post : OAction      -- initialize post
    posted : OAction    -- post successful
    ack : OAction

  -- The "output buffer functor". The type ⊤ indicates a "fault" or unallowed
  -- action.
  OB : Set → Set
  OB X = (OAction → ⊤ ⊎ X)

  -- The step function/morphism for the output buffer
  δ₀ : Buffer Msg' → OB (Buffer Msg')
  δ₀ (buffer [] idle) (insert m)          = inj₂ (buffer [] transmit⟨ m ⟩)
  δ₀ (buffer [] s) (insert m)             = inj₂ (enq m (buffer [] s))
  δ₀ (buffer (m' ∷ msgs) idle) (insert m) = inj₂ (enq m (buffer msgs transmit⟨ m' ⟩))
  δ₀ (buffer (m' ∷ msgs) s) (insert m)    = inj₂ (enq m (buffer (m' ∷ msgs) s))
  δ₀ (buffer [] idle) post                = inj₁ tt
  δ₀ ob@(buffer (m ∷ msgs) idle) post     = inj₂ (transmitNext ob λ ())
  δ₀ (buffer msgs blocking) post          = inj₁ tt
  δ₀ (buffer msgs transmit⟨ x ⟩) post     = inj₁ tt
  δ₀ (buffer msgs _) posted               = inj₂ (buffer msgs blocking)
  δ₀ (buffer msgs idle) ack               = inj₁ tt
  δ₀ (buffer [] blocking) ack             = inj₂ (buffer [] idle)
  δ₀ (buffer (m ∷ msgs) blocking) ack     = inj₂ (buffer (m ∷ msgs) idle)
  δ₀ (buffer msgs transmit⟨ x ⟩) ack      = inj₁ tt

