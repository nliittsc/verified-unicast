module Protocols.CausalHistory.Protocol where

open import Function
open import Data.List
open import Data.List.Properties
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
-- open import Data.String
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟨_⟩)
open import Relation.Nullary


open import Machine.Step
open import Machine.Core


{- Attempt to define a simple causal history protocol.

  * Messages are abstract, but should have decidable equality
  * Local state is a history, and a delay queue
  * Messages are removed from the delay queue when the causal
    history on the message is a subset of the causal history
    on the process
  
-}

-- FIXME: A lot of this machinery can probably be generalized and sent to Core

module Impl (RawMsg : Set) (AppEvent : Set)
            (decider : (m₁ m₂ : RawMsg) → Dec (m₁ ≡ m₂))
            (evt-decider : (e₁ e₂ : AppEvent) → Dec (e₁ ≡ e₂)) where

  Message = Msg RawMsg
  Evt = Event RawMsg AppEvent
  History = List Evt
  DelayQueue = List Evt


  -- Message and event construction is an injective operation.
  -- FIXME: Is there a way to avoid these lemmas with pattern matching?
  msg-inj₁ : ∀{A : Set} {s₁ s₂ r₁ r₂} {p₁ p₂ : A} → msg s₁ r₁ p₁ ≡ msg s₂ r₂ p₂ → s₁ ≡ s₂
  msg-inj₁ refl = refl
  msg-inj₂ : ∀{A : Set} {s₁ s₂ r₁ r₂} {p₁ p₂ : A} → msg s₁ r₁ p₁ ≡ msg s₂ r₂ p₂ → r₁ ≡ r₂
  msg-inj₂ refl = refl
  msg-inj₃ : ∀{A : Set} {s₁ s₂ r₁ r₂} {p₁ p₂ : A} → msg s₁ r₁ p₁ ≡ msg s₂ r₂ p₂ → p₁ ≡ p₂
  msg-inj₃ refl = refl
  send-inj : ∀{A E : Set} {m₁ m₂ : Msg A} {e₁ e₂ : Event A E} →
              e₁ ≡ send⟨ m₁ ⟩ → e₁ ≡ e₂ → e₂ ≡ send⟨ m₂ ⟩ → m₁ ≡ m₂
  send-inj refl refl refl = refl
  recv-inj : ∀{A E : Set} {m₁ m₂ : Msg A} {e₁ e₂ : Event A E} →
              e₁ ≡ recv⟨ m₁ ⟩ → e₁ ≡ e₂ → e₂ ≡ recv⟨ m₂ ⟩ → m₁ ≡ m₂
  recv-inj refl refl refl = refl
  evt-inj : ∀{A : Set} {a₁ a₂ : AppEvent} {e₁ e₂ : Event A AppEvent} →
            e₁ ≡ evt⟨ a₁ ⟩ → e₁ ≡ e₂ → e₂ ≡ evt⟨ a₂ ⟩ → a₁ ≡ a₂
  evt-inj refl refl refl = refl
  msg-cong : ∀{A : Set} {s₁ s₂ r₁ r₂} {p₁ p₂ : A} → s₁ ≡ s₂ → r₁ ≡ r₂ → p₁ ≡ p₂ →
             msg r₁ s₁ p₁ ≡ msg r₂ s₂ p₂
  msg-cong refl refl refl = refl

  -- We can compare messages
  _≡M?_ : (m₁ m₂ : Message) → Dec (m₁ ≡ m₂)
  msg s₁ r₁ pay₁ ≡M? msg s₂ r₂ pay₂ with s₁ ≟ s₂
  msg s₁ r₁ pay₁ ≡M? msg s₂ r₂ pay₂ | yes p with r₁ ≟ r₂
  msg s₁ r₁ pay₁ ≡M? msg s₂ r₂ pay₂ | yes p | yes q with decider pay₁ pay₂
  msg s₁ r₁ pay₁ ≡M? msg s₂ r₂ pay₂ | yes p | yes q | yes r = yes (msg-cong q p r)
  msg s₁ r₁ pay₁ ≡M? msg s₂ r₂ pay₂ | yes p | yes q | no ¬r = no (λ m₁≡m₂ → ¬r (msg-inj₃ m₁≡m₂))
  msg s₁ r₁ pay₁ ≡M? msg s₂ r₂ pay₂ | yes p | no ¬q         = no (λ m₁≡m₂ → ¬q (msg-inj₂ m₁≡m₂))
  msg s₁ r₁ pay₁ ≡M? msg s₂ r₂ pay₂ | no ¬p                 = no (λ m₁≡m₂ → ¬p (msg-inj₁ m₁≡m₂))

  -- We can compare events
  _≡?_ : (e₁ e₂ : Evt) → Dec (e₁ ≡ e₂)
  send⟨ m ⟩ ≡? send⟨ m₁ ⟩ with m ≡M? m₁
  ... | yes p             = yes (cong send⟨_⟩ p)
  ... | no ¬p             = no (λ z → ¬p (send-inj refl z refl))
  send⟨ m ⟩ ≡? recv⟨ m₁ ⟩ = no (λ ())
  send⟨ m ⟩ ≡? evt⟨ m₁ ⟩  = no (λ ())
  recv⟨ m ⟩ ≡? send⟨ m₁ ⟩ = no (λ ())
  recv⟨ m ⟩ ≡? recv⟨ m₁ ⟩ with m ≡M? m₁
  ... | yes p             = yes (cong recv⟨_⟩ p)
  ... | no ¬p             = no (λ z → ¬p (recv-inj refl z refl))
  recv⟨ m ⟩ ≡? evt⟨ m₁ ⟩  = no (λ ())
  evt⟨ m ⟩ ≡? send⟨ m₁ ⟩  = no (λ ())
  evt⟨ m ⟩ ≡? recv⟨ m₁ ⟩  = no (λ ())
  evt⟨ a ⟩ ≡? evt⟨ a₁ ⟩ with evt-decider a a₁
  ... | yes p             = yes (cong evt⟨_⟩ p)
  ... | no ¬p             = no (λ z → ¬p (evt-inj refl z refl))


  {- We have a decision procedure for checking if an event
     is in the history of some object
  -}
  _∈?_ : (e : Evt) → (h : History) → Dec (e ∈ h)
  e ∈? [] = no (λ ())
  e ∈? (e' ∷ h) with e ≡? e'
  e ∈? (e' ∷ h) | yes p = yes (here p)
  e ∈? (e' ∷ h) | no ¬p with e ∈? h
  e ∈? (e' ∷ h) | no ¬p | yes q = yes (there q)
  e ∈? (e' ∷ h) | no ¬p | no ¬q =
    no (λ z → case z of λ { (here px) → ¬p px ; (there a) → ¬q a })

  -- TODO: Describe a decision procedure for checking if one causal history
  --       is a subset of another causal history

  -- Our application dependent state is the history and queue
  record AppState : Set where
    constructor ⟨_,_⟩
    field
      hist : History
      dq   : DelayQueue

  open AppState public

  -- parameterizing our state
  State = LState RawMsg AppEvent AppState




