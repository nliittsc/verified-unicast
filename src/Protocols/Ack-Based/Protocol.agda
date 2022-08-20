module Protocols.Ack-Based.Protocol where

open import Function
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.List
open import Data.List.Properties
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.Maybe
open import Data.Maybe.Properties
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟨_⟩)
open import Relation.Nullary
-- open import Relation.Unary

open import Machine.Core
open import Machine.Step


data CommState : Set where
  blocked : CommState
  OK      : CommState


-- (Expr , Proc)  --> (Expr' , Proc)
-- (Expr , Proc) --> (Expr' , Proc) , payload

-- send M to N : Expr
-- sn

-- m <- receive

module Impl (Payload : Set)
            (AppState : Set)
            (init : AppState)
            (silent-step : AppState → AppState)
            (recv-step : AppState → Payload → AppState) where


  -- Messages contain the sender, receiver, and the payload
  Message = Msg Payload

  record Buffer : Set where
    constructor buf
    field
      queue : List Message
      cstate : CommState

  open Buffer public

  enqueue : Buffer → Message → Buffer
  enqueue (buf q cs) m = buf (q ++ [ m ]) cs

  dequeue : Buffer → (Maybe Message) × Buffer
  dequeue b@(buf [] cs) = nothing , b
  dequeue (buf (m ∷ ms) cs) = just m , buf ms cs

  record Proc : Set where
    constructor pr
    field
      pid : ℕ
      obr : Buffer
      ibr : Buffer
      state : AppState

  open Proc public
      
  {-
    Going for a more "coalgebraic" approach to the protocol: each event is encoded
    as a particular (functional) type which modifies the state.
  -}

  -- Buffer Protocol Events: send, insert, post, ack, get, deliver, recv
 
  insert : Proc → Message → Proc
  insert (pr n ob ib s) m = pr n (enqueue ob m) ib s

  insert-correct : ∀{n ob ib s m} → insert (pr n ob ib s) m ≡ pr n (enqueue ob m) ib s
  insert-correct = refl

  -- If the buffers need to live "separately", then we can write a helper function create the record
  insert′ : ℕ → Buffer → Buffer → AppState → Message → Proc
  insert′ n ob ib s m = insert (pr n ob ib s) m

  {- Left indicates successful post, Right indicates failed post (due to blocking or emptiness)
      This design is inspired from "Introduction to Coalgebra"
  -}
  post : Proc → (Message × Proc) ⊎ Proc
  post (pr n ob ib s) with cstate ob
  post proc@(pr n ob ib s)           | blocked = inj₂ proc
  post proc@(pr n (buf [] _) ib s)   | OK      = inj₂ proc
  post (pr n (buf (m ∷ ms) cs) ib s) | OK      = inj₁ (m , pr n (buf ms blocked) ib s)

  -- This indicates whether a process can post something
  data Can-Post : Proc → Set where
    postable : ∀{n m ms ib s} proc →
               proc ≡ (pr n (buf (m ∷ ms) OK) ib s) →
               Can-Post proc

  post-correctˡ : ∀ proc → Can-Post proc → (∃₂ λ m proc′ → post proc ≡ inj₁ (m , proc′))
  post-correctˡ .(pr _ (buf (_ ∷ _) OK) _ _) (postable .(pr _ (buf (_ ∷ _) OK) _ _) refl) = _ , pr _ (buf _ blocked) _ _ , refl

  post-correctʳ : ∀ proc → (∃₂ λ m proc′ → post proc ≡ inj₁ (m , proc′)) → Can-Post proc
  post-correctʳ proc (m , pr pid₁ obr₁ ibr₁ state₁ , prf) = postable proc {!!}

  open import Verdi

  data Input′ : Set where
    tickProc tickOB tickIB : Input′

  -- Inputs : things that happen to the thread
  -- Outputs : things that the thread elects to do?

  Node = ℕ
  State : Node → Set
  State = λ x → Proc
  Input = Input′
  Output = ⊤
  Message' = Message ⊎ ⊤


  -- **** Compositional abstraction for threads ****
  -- TODO: A better abstraction that represents both network communication
  -- and local thread communication (IPC)

  -- btw: get the concurrency haskell book to learn about STM

  -- the `tickProc` input here should be entirely application driven
  -- the application tells us how the process ticks/steps forward
  -- ie the app tells us when we want to receive a message/send a message
  HandleInp : (n : Node) → State n → Input
              → (State n × Output × List (Packet Node Message'))
  -- need module parameters that allows tickProc to be entirely application driven
  HandleInp n s tickProc = {!!}
  HandleInp n s tickOB with post s
  ... | inj₁ (m , s') = s' , tt , [ n ⇒ receiver m ⦂ inj₁ m ]
  ... | inj₂ _        = s , tt , []
  HandleInp n s tickIB = {!!}


  
  HandleMsg : (n : Node) → State n → Packet Node Message'
              → (State n × Output × List (Packet Node Message'))
  HandleMsg n s (src ⇒ dst ⦂ inj₁ m) = {!!}
  HandleMsg n s (src ⇒ dst ⦂ inj₂ tt) = {!!}

  BufferApp : App
  BufferApp = record
                { Node = Node
                ; _≟_ = _≟_
                ; State = State
                ; Msg = Message'
                ; Input = Input
                ; Output = Output
                ; initState = λ n → pr n (buf [] OK) (buf [] OK) init
                ; HandleInp = HandleInp
                ; HandleMsg = HandleMsg
                }







