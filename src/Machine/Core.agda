module Machine.Core where

open import Data.Bool
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.List
open import Data.Sum
open import Data.Product
open import Data.Maybe
open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟨_⟩)
open ≡-Reasoning

-- Convenience
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []


--- Types ---

private
  variable
    A B C : Set

Pid = ℕ

  --- Messages ---

record Msg (A : Set) : Set where
  constructor msg
  field
    sender : ℕ
    receiver : ℕ
    payload : A


-- The main module. A and S are types which depend
-- on the application. We assume some way of changing internal state.
module Δ (R S : Set) (sstep : S → Msg R → S) (produce : S → List (Msg R)) where

  --- Buffers ---

  data BState : Set where
    idle     : BState
    blocking : BState
    transmit⟨_⟩ : Msg R → BState

  -- Transmit is not equal to any other state
  idle≢transmit : ∀ x → idle ≢ transmit⟨ x ⟩
  idle≢transmit x = λ ()
  blocking≢transmit : ∀ x → blocking ≢ transmit⟨ x ⟩
  blocking≢transmit x = λ ()

    
  record Buffer (A : Set) : Set where
    constructor buffer
    field
      queue : List A
      state : BState

  open Buffer public

  -- Provides a witness to whether the queue is empty or not
  empty : (b : Buffer A) → Dec (queue b ≡ [])
  empty buf with queue buf
  empty buf | []      = yes refl
  empty buf | (_ ∷ _) = no (λ ())

  -- Provides a witness to whether the queue is blocked or not
  blocked : (b : Buffer A) → Dec (state b ≡ blocking)
  blocked b with state b
  ...          | idle = no (λ ())
  ...          | blocking = yes refl
  ...          | transmit⟨ _ ⟩ = no (λ ())

  -- Provides a witness to whether the queue needs to send a message
  needTransmit : (b : Buffer A) → Dec (∃ λ x → state b ≡ transmit⟨ x ⟩)
  needTransmit b with state b
  ... | idle          = no (λ x → idle≢transmit (proj₁ x) (proj₂ x))
  ... | blocking      = no (λ x → blocking≢transmit (proj₁ x) (proj₂ x))
  ... | transmit⟨ x ⟩ = yes (x , refl)

  enq : A → Buffer A → Buffer A
  enq x (buffer queue₁ state₁) = buffer (queue₁ ++ [ x ]) state₁

  deq : Buffer A → (Maybe A × Buffer A)
  deq buf with queue buf
  deq buf | []       = (nothing , buf)
  deq buf | (x ∷ xs) = (just x , record buf { queue = xs })

  -- Dequeue is nothing only when the buffer is empty
  deq-nothing⇒empty : ∀(b : Buffer A) → deq b ≡ (nothing , b) → queue b ≡ []
  deq-nothing⇒empty b prf with queue b
  ... | [] = refl
  
 
  -- If prove that the queue is not empty, then prepare the next transmission
  transmitNext : (b : Buffer (Msg R)) → queue b ≢ [] → Buffer (Msg R)
  transmitNext b b≢[] with queue b
  ... | [] = ⊥-elim (b≢[] refl)
  ... | x ∷ xs = buffer xs transmit⟨ x ⟩

  --- Machine Specification / CoAlgebra ---
  record PState : Set where
    constructor process
    field
      inbuf : Buffer (Msg R)
      outbuf : Buffer (Msg R)
      internal : S  -- Application dependent internal state

  open PState public
