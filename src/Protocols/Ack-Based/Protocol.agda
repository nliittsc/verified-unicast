open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟨_⟩)
open import Relation.Nullary

module Protocols.Ack-Based.Protocol (Msg : Set)
                                    (State : Set)
                                    (step : State → Msg → State)
                                    (gen-msgs : State → List (ℕ × Msg))
                                    (_≟ₘ_ : (m₁ : Msg) → (m₂ : Msg) → Dec (m₁ ≡ m₂)) where


Pid = ℕ

data CommState : Set where
  ok : CommState
  waiting-on : Pid → CommState

-- Pid is the sender of the ack
data Ack : Set where
  ack-msg : Pid → Ack

record Packet : Set where
  constructor ⌊_,_,_⌋
  field
    sender  : Pid
    dest    : Pid
    payload : Msg

open Packet public

Buffer = CommState × List Packet

-- ID, Abstract State, InputBuffer, Output Buffer
record Proc : Set where
  constructor ⟫
  field
    pid : Pid
    state : State
    inbuf : Buffer
    oubuf : Buffer

open Proc public

-- Each function below roughly corresponds to an event from the paper
-- The intended order of events is:
-- send -> insert -> post -> get -> ack -> deliver -> receive
-- Note: receive and deliver have swapped semantics compared to what we are used to

-- Insert into a buffer. Also serves as the `get` event for input buffers
insert : Buffer → Packet → Buffer
insert (s , q) pckt = (s , q ++ [ pckt ])

-- Posting a message from a buffer to the network
post : Buffer → Buffer × Maybe Packet
post b@(_ , []) = b , nothing
post b@(waiting-on _ , _) = b , nothing
post (ok , (pckt ∷ q)) = (waiting-on (dest pckt) , q) , just pckt

-- If the ack message matches, unblock the buffer
ack : Buffer → Ack → Buffer
ack b@(waiting-on i , q) (ack-msg j) with i ≟ j
... | yes _ = (ok , q)
... | no  _ = b
ack b@(_ , _) _ = b

-- A send is really just a enqueue
send : Proc → Pid → Msg → Proc × Packet
send proc j m =
  let pckt = ⌊ pid proc , j , m ⌋
      proc′ = record proc { oubuf = insert (oubuf proc) pckt }
  in proc′ , pckt

-- A get (from the network) enqueues into the input buffer and generates the acknowledgement
get : Proc → Packet → Proc × Ack
get proc pckt =
  let proc′ = record proc { inbuf = insert (inbuf proc) pckt }
  in proc′ , ack-msg (pid proc′)

-- A deliver (request) removes from the input buffer
deliver : Buffer → Buffer × Maybe Packet
deliver b@(_ , []) = b , nothing
deliver (s , pckt ∷ q) = (s , q) , just pckt

-- a receive consumes a message, updates state, and generates to-be-sent messages
receive : Proc → Packet → Proc × List (Pid × Msg)
receive proc pckt =
  let s′ = step (state proc) (payload pckt)
      proc′ = record proc { state = s′ }
      stack = gen-msgs s′
  in proc′ , stack
