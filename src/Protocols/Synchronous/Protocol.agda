open import Data.List
open import Data.Nat
open import Data.Fin
open import Data.Product
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟨_⟩)

module Synchronous.Protocol (num-sites : ℕ)
                            (Msg : Set)
                            (State : Set)
                            (appstep : State → State)
                            (step : State → Msg → State)
                            (gen-msg : State → Fin num-sites × Msg) where


Site = Fin num-sites


data ProtocolMsg : Set where
  ack : ProtocolMsg
  handshake : Msg → ProtocolMsg

data CommState : Set where
  ok : CommState
  sending : Site → ProtocolMsg → CommState
  blocked-on : Site → CommState

record Packet : Set where
  constructor _⇒_∶_
  field
    sender  : Site
    dest    : Site
    payload : ProtocolMsg


open Packet public

record LocalState : Set where
  constructor ⟫
  field
    self  : Site
    state : State
    comm  : CommState

open LocalState public

-- These are local transitions in local state, so no need to implement
-- the message buffer
data _⟶_ : LocalState → LocalState → Set where
  tick : ∀ i s →
         ⟫ i s ok ⟶ ⟫ i (appstep s) ok

  send-tick : ∀ i s → let (j , m) = gen-msg s in
              ⟫ i s ok ⟶ ⟫ i s (sending j (handshake m))
              
  send-ack : ∀ i j s →  ⟫ i s (sending j ack) ⟶ ⟫ i s ok

  send-msg : ∀ i j s m → ⟫ i s (sending j (handshake m)) ⟶ ⟫ i s (blocked-on j)

  recv-ack : ∀ i j s pckt →
             pckt ≡ j ⇒ i ∶ ack → 
             ⟫ i s (blocked-on j) ⟶ ⟫ i s ok

  recv-msg : ∀ i j s pckt m →
             pckt ≡ j ⇒ i ∶ (handshake m) →
             ⟫ i s ok ⟶ ⟫ i (step s m) (sending j ack)


 send : OKState → BlockState
  
