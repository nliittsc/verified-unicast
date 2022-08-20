module Applications.Language.Syntax where

open import Data.Char
open import Data.Fin as F
open import Data.List
open import Data.Nat
open import Data.Product
open import Data.String
open import Data.Vec as V


{-
  Following the "Featherweight Erlang" example, the language needs:
    1. Identifiers
    2. Values
    3. Messages (tuples of values)
    4. Receive Patterns  (is this a selective receive?)
    5. Terms
    6. Configurations
-}

{-
  The semantics of send and receive should probably be ignorant to the actual protocol being used, which
  will happen "under the hood". This *should* allow us to indiscriminately swap out protocols, though
  perhaps there's some parameterization (by the protocol) that needs to be tracked.
-}


data Id : Set where
  ⟨_⟩ : String → Id    -- Variable
  ‵_ : ℕ → Id          -- Process ID
  *_ : String → Id     -- Reference

data Val : Set where
  υ : Id → Val
  α : Char → Val

Message : Set
Message = List Val


-- TODO: Figure out what to do about selective receives

mutual
  data RecvPattern : Set where
    -- `recv M ⟶ P` = receive a message M and then continue as process P 
    recv_⟶_ : Message → Term → RecvPattern
    -- _∣_      : RecvPattern → RecvPattern → RecvPattern

  data Term : Set where
    ⟦_⟧ : Val → Term  -- values
    _!_▸_ : Id → Message → Term → Term  -- Sending a message
    ⟫ : RecvPattern → Term

-- Packets make up the contents which will actually be transported over the network
record Packet : Set where
  constructor pck
  field
    sender   : ℕ
    receiver : ℕ
    payload  : Message

Mailbox : Set
Mailbox = List Packet

-- The configuration for an "erlang" program consisting of a PID, mailbox, and term
Config : Set
Config = ℕ × Mailbox × Term

System : ℕ → Set
System n = V.Vec Config n


-- System reductions
data _⟿_ {n : ℕ} : Config → Config → Set where
  -- send : ∀{i j Π} → 





