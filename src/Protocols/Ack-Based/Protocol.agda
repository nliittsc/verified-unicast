module Protocols.Ack-Based.Protocol where

open import Function
open import Data.Empty
open import Data.List
open import Data.List.Properties
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.Maybe
open import Data.Maybe.Properties
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟨_⟩)
open import Relation.Nullary
-- open import Relation.Unary

open import Machine.Core
open import Machine.Step

enqueue : ∀{A : Set} → A → List A → List A
enqueue a xs = xs ++ [ a ]

dequeue : ∀{A : Set} → List A → (Maybe A) × List A
dequeue []       = (nothing , [])
dequeue (a ∷ xs) = (just a , xs)

module Impl (RawMsg : Set)
            (decider : (m₁ m₂ : RawMsg) → Dec (m₁ ≡ m₂)) where



  Message = Msg RawMsg

  -- The events of our transition system
  data AppEvent : Set where
    -- insert⟨_⟩  : Message → AppEvent
    post-next   : AppEvent
    ack-from⟨_⟩ : Pid → AppEvent
    get⟨_⟩      : Message → AppEvent
    recv-req    : AppEvent

  Evt = Event RawMsg AppEvent
  History = List Evt

  data BufState : Set where
    ok✓         : BufState
    waiting-on⟨_⟩ : Pid → BufState

  record OutBuf : Set where
    constructor ob
    field
      ob-state  : BufState
      out-queue : List Message

  open OutBuf public
  
  record InBuf : Set where
    constructor ib
    field
      ib-state : BufState
      in-queue : List Message

  open InBuf public
  
  -- Our application dependent state is input-output buffers
  record AppState : Set where
    constructor st
    field
      obuf   : OutBuf
      ibuf   : InBuf

  open AppState public

  

  {- We need an "application specific" transition function. The function
     is partial, hence the use of Maybe.

     Properties:
       1. Inserting into the out-buffer is always possible
       2. Getting a message from the network is always possible
       3. Input-buffer is never blocked when non-empty
       4. Output-buffer always blocks after a post event
       5. Output-buffer always unblocks when an acknowledgement is seen

     Question: Should this also produce the next "Round" of events that need to be processed?
  -}
  δₐ : AppState → Evt → Maybe AppState
  δₐ (st (ob sₒ qₒ) ibuffer) send⟨ m ⟩                = let obuffer' = ob sₒ (enqueue m qₒ) in just (st obuffer' ibuffer)
  δₐ (st obuffer ibuffer) recv⟨ m ⟩                  = nothing  -- this affects the history, but not the buffers
  δₐ (st (ob ok✓ []) _) evt⟨ post-next ⟩             = nothing
  δₐ (st (ob ok✓ (m ∷ qₒ)) ibuffer) evt⟨ post-next ⟩ = let obuffer' = ob waiting-on⟨ receiver m ⟩ qₒ in just (st obuffer' ibuffer)
  δₐ (st (ob waiting-on⟨ _ ⟩ _) _) evt⟨ post-next ⟩  = nothing
  δₐ (st (ob ok✓ _) _) evt⟨ ack-from⟨ q ⟩ ⟩ = nothing
  δₐ (st (ob waiting-on⟨ j ⟩ qₒ) ibuffer) evt⟨ ack-from⟨ j' ⟩ ⟩ with j ≟ j'
  ... | yes p                                        = just (st (ob ok✓ qₒ) ibuffer)
  ... | no ¬p                                        = nothing
  δₐ (st obuffer (ib sᵢ qᵢ)) evt⟨ get⟨ m ⟩ ⟩           = let ibuffer' = ib sᵢ (enqueue m qᵢ) in just (st obuffer ibuffer')
  δₐ (st _ (ib ok✓ [])) evt⟨ recv-req ⟩              = nothing
  δₐ (st obuffer (ib ok✓ (m ∷ qᵢ))) evt⟨ recv-req ⟩   = let ibuffer' = ib ok✓ qᵢ in just (st obuffer ibuffer')
  δₐ (st _ (ib _ _)) evt⟨ recv-req ⟩                 = nothing


  -- Local, application dependent transitions
  data _=[_]⇒_ : AppState → Evt → AppState → Set where
    send-rule : ∀{m sₒ qₒ ibuffer} →
               let obuffer' = ob sₒ (enqueue m qₒ)
               in st (ob sₒ qₒ) ibuffer =[ send⟨ m ⟩ ]⇒ st obuffer' ibuffer

    post-rule : ∀{m qₒ ibuffer} →
                let obuffer' = ob waiting-on⟨ receiver m ⟩ qₒ
                in st (ob ok✓ (m ∷ qₒ)) ibuffer =[ evt⟨ post-next ⟩ ]⇒ st obuffer' ibuffer

    ack-rule : ∀{qₒ j ibuffer} →
               let obuffer' = ob ok✓ qₒ
               in st (ob waiting-on⟨ j ⟩ qₒ) ibuffer =[ evt⟨ ack-from⟨ j ⟩ ⟩ ]⇒ st obuffer' ibuffer

    get-rule : ∀{m sᵢ qᵢ obuffer} →
               let ibuffer' = ib sᵢ (enqueue m qᵢ)
               in st obuffer (ib sᵢ qᵢ) =[ evt⟨ get⟨ m ⟩ ⟩ ]⇒ st obuffer ibuffer'

    req-rule : ∀{m qᵢ obuffer} →
               let ibuffer' = ib ok✓ qᵢ
               in st obuffer (ib ok✓ (m ∷ qᵢ)) =[ evt⟨ recv-req ⟩ ]⇒ st obuffer ibuffer'
               

  -- Some needed injectivity lemmas
  st-ibuf-injective : ∀{obuf₁ ibuf₁ obuf₂ ibuf₂} → st obuf₁ ibuf₁ ≡ st obuf₂ ibuf₂ → ibuf₁ ≡ ibuf₂
  st-ibuf-injective refl = refl
  st-obuf-injective : ∀{obuf₁ ibuf₁ obuf₂ ibuf₂} → st obuf₁ ibuf₁ ≡ st obuf₂ ibuf₂ → obuf₁ ≡ obuf₂
  st-obuf-injective refl = refl
  ob-s-injective : ∀{s s' q q'} → ob s q ≡ ob s' q' → s ≡ s'
  ob-s-injective refl = refl
  ob-q-injective : ∀{s s' q q'} → ob s q ≡ ob s' q' → q ≡ q'
  ob-q-injective refl = refl

  app-step-correctˡ : ∀ s s' e → δₐ s e ≡ just s' → s =[ e ]⇒ s'
  -- SEND CASES
  -- Next 2 cases cannot happen b.c. enq into a list can not yield an empty list
  app-step-correctˡ (st (ob _ [])      _) (st (ob _ []) _) send⟨ m ⟩ ()
  app-step-correctˡ (st (ob _ (_ ∷ _)) _) (st (ob _ []) _) send⟨ m ⟩ ()
  
  -- Next case is a "straightfoward" proof by using substitution 3 times
  -- FIXME? : Holy shit this proof is terrible. Why is it so awful? I feel like a villain writing this
  app-step-correctˡ (st (ob sₒ qₒ) ibuf₁) (st (ob sₒ' (m' ∷ qₒ')) ibuf₂) send⟨ m ⟩ δₐse≡s' = prf
    where
      sₒ≡sₒ' : sₒ ≡ sₒ'
      sₒ≡sₒ' = ob-s-injective (st-obuf-injective (just-injective δₐse≡s'))
      qₒ≡qₒ' : enqueue m qₒ ≡ m' ∷ qₒ'
      qₒ≡qₒ' = ob-q-injective (st-obuf-injective (just-injective δₐse≡s'))
      ibuf₁≡ibuf₂ : ibuf₁ ≡ ibuf₂
      ibuf₁≡ibuf₂ = st-ibuf-injective (just-injective δₐse≡s')
      prf : st (ob sₒ qₒ) ibuf₁ =[ send⟨ m ⟩ ]⇒ st (ob sₒ' (m' ∷ qₒ')) ibuf₂
      prf = subst (λ sₒ' → st (ob sₒ qₒ) ibuf₁ =[ send⟨ m ⟩ ]⇒ st (ob sₒ' (m' ∷ qₒ')) ibuf₂) sₒ≡sₒ' prf₁
        where
          prf₁ : st (ob sₒ qₒ) ibuf₁ =[ send⟨ m ⟩ ]⇒ st (ob sₒ (m' ∷ qₒ')) ibuf₂
          prf₁ = subst (λ ibuf₂ → st (ob sₒ qₒ) ibuf₁ =[ send⟨ m ⟩ ]⇒ st (ob sₒ (m' ∷ qₒ')) ibuf₂ ) ibuf₁≡ibuf₂ prf₂
            where
              prf₂ : st (ob sₒ qₒ) ibuf₁ =[ send⟨ m ⟩ ]⇒ st (ob sₒ (m' ∷ qₒ')) ibuf₁
              prf₂ = subst (λ m'∷qₒ' → st (ob sₒ qₒ) ibuf₁ =[ send⟨ m ⟩ ]⇒ st (ob sₒ m'∷qₒ') ibuf₁) qₒ≡qₒ' send-rule

  -- POST CASES
  -- Next 6 cases cannot happen due to discrepancies in the output buffer state and where δₐ is defined
  app-step-correctˡ (st (ob ok✓ []) _)             (st (ob ok✓ []) _)                 evt⟨ post-next ⟩ ()
  app-step-correctˡ (st (ob ok✓ []) _)             (st (ob waiting-on⟨ _ ⟩ []) _)      evt⟨ post-next ⟩ ()
  app-step-correctˡ (st (ob waiting-on⟨ _ ⟩ []) _) (st (ob _ []) _)                    evt⟨ post-next ⟩ ()
  app-step-correctˡ (st (ob ok✓ []) _)             (st (ob ok✓ (_ ∷ _)) _)             evt⟨ post-next ⟩ ()
  app-step-correctˡ (st (ob ok✓ []) _)             (st (ob waiting-on⟨ _ ⟩ (_ ∷ _)) _) evt⟨ post-next ⟩ ()
  app-step-correctˡ (st (ob waiting-on⟨ _ ⟩ []) _) (st (ob s' (_ ∷ _)) _)              evt⟨ post-next ⟩ ()

  -- These two cases actually do happen
  app-step-correctˡ (st (ob ok✓ (_ ∷ _)) _) (st (ob waiting-on⟨ _ ⟩ [])      _) evt⟨ post-next ⟩ refl = post-rule
  app-step-correctˡ (st (ob ok✓ (_ ∷ _)) _) (st (ob waiting-on⟨ _ ⟩ (_ ∷ _)) _) evt⟨ post-next ⟩ refl = post-rule

  -- ACKNOWLEDGE CASES
  app-step-correctˡ (st (ob ok✓ []) ibuf₁) (st (ob ok✓ []) ibuf₂) evt⟨ ack-from⟨ j ⟩ ⟩ ()
  app-step-correctˡ (st (ob ok✓ []) ibuf₁) (st (ob ok✓ (x ∷ out-queue₁)) ibuf₂) evt⟨ ack-from⟨ j ⟩ ⟩ ()
  app-step-correctˡ (st (ob ok✓ (x ∷ out-queue₂)) ibuf₁) (st (ob ok✓ out-queue₁) ibuf₂) evt⟨ ack-from⟨ j ⟩ ⟩ ()
  app-step-correctˡ (st (ob waiting-on⟨ x ⟩ out-queue₂) ibuf₁) (st (ob ok✓ out-queue₁) ibuf₂) evt⟨ ack-from⟨ j ⟩ ⟩ δₐse≡s' = {!!}
  app-step-correctˡ (st (ob ok✓ []) ibuf₁) (st (ob waiting-on⟨ x ⟩ []) ibuf₂) evt⟨ ack-from⟨ j ⟩ ⟩ ()
  app-step-correctˡ (st (ob ok✓ (x₁ ∷ out-queue₂)) ibuf₁) (st (ob waiting-on⟨ x ⟩ []) ibuf₂) evt⟨ ack-from⟨ j ⟩ ⟩ ()
  app-step-correctˡ (st (ob ok✓ []) ibuf₁) (st (ob waiting-on⟨ x ⟩ (x₁ ∷ out-queue₁)) ibuf₂) evt⟨ ack-from⟨ j ⟩ ⟩ ()
  app-step-correctˡ (st (ob ok✓ (x₂ ∷ out-queue₂)) ibuf₁) (st (ob waiting-on⟨ x ⟩ (x₁ ∷ out-queue₁)) ibuf₂) evt⟨ ack-from⟨ j ⟩ ⟩ ()
  app-step-correctˡ (st (ob waiting-on⟨ j ⟩ []) _) (st (ob waiting-on⟨ x ⟩ []) _) evt⟨ ack-from⟨ j' ⟩ ⟩ δₐse≡s' with j ≟ j'
  app-step-correctˡ (st (ob waiting-on⟨ j ⟩ []) _) (st (ob waiting-on⟨ x ⟩ []) _) evt⟨ ack-from⟨ j' ⟩ ⟩ () | yes p
  app-step-correctˡ (st (ob waiting-on⟨ j ⟩ []) _) (st (ob waiting-on⟨ x ⟩ []) _) evt⟨ ack-from⟨ j' ⟩ ⟩ () | no ¬p
  app-step-correctˡ (st (ob waiting-on⟨ j ⟩ []) _) (st (ob waiting-on⟨ x ⟩ (_ ∷ _)) _) evt⟨ ack-from⟨ j' ⟩ ⟩ δₐse≡s' with j ≟ j'
  app-step-correctˡ (st (ob waiting-on⟨ j ⟩ []) _) (st (ob waiting-on⟨ x ⟩ (_ ∷ _)) _) evt⟨ ack-from⟨ j' ⟩ ⟩ () | yes p
  app-step-correctˡ (st (ob waiting-on⟨ j ⟩ []) _) (st (ob waiting-on⟨ x ⟩ (_ ∷ _)) _) evt⟨ ack-from⟨ j' ⟩ ⟩ () | no ¬p
  app-step-correctˡ (st (ob waiting-on⟨ j ⟩ (_ ∷ _)) _) (st (ob waiting-on⟨ x ⟩ []) _) evt⟨ ack-from⟨ j' ⟩ ⟩ δₐse≡s' with j ≟ j
  ... | yes p = {!!}
  ... | no ¬p = {!!}
  app-step-correctˡ (st (ob waiting-on⟨ j ⟩ (x₂ ∷ out-queue₂)) ibuf₁) (st (ob waiting-on⟨ x ⟩ (x₃ ∷ out-queue₁)) ibuf₂) evt⟨ ack-from⟨ j' ⟩ ⟩ δₐse≡s' = {!!}

  -- GET CASES
  app-step-correctˡ s s' evt⟨ get⟨ m ⟩ ⟩ δₐse≡s' = {!!}

  -- RECEIVE CASES
  app-step-correctˡ s s' evt⟨ recv-req ⟩ δₐse≡s' = {!!}

  app-step-correctʳ : ∀ s s' e → s =[ e ]⇒ s' → δₐ s e ≡ just s'
  app-step-correctʳ .(st (ob _ _) _) .(st (ob _ (enqueue _ _)) _) .(send⟨ _ ⟩) send-rule                           = refl
  app-step-correctʳ .(st (ob ok✓ (m ∷ _)) _) .(st (ob waiting-on⟨ receiver m ⟩ _) _) .(evt⟨ post-next ⟩) (post-rule {m}) = refl
  app-step-correctʳ .(st (ob waiting-on⟨ j ⟩ _) _) .(st (ob ok✓ _) _) .(evt⟨ ack-from⟨ j ⟩ ⟩) (ack-rule {j = j}) with j ≟ j
  ... | yes p = refl
  ... | no ¬p = ⊥-elim (¬p refl)
  app-step-correctʳ .(st _ (ib _ _)) .(st _ (ib _ (enqueue _ _))) .(evt⟨ get⟨ _ ⟩ ⟩) get-rule = {!!}
  app-step-correctʳ .(st _ (ib ok✓ (_ ∷ _))) .(st _ (ib ok✓ _)) .(evt⟨ recv-req ⟩) req-rule = {!!}

  app-step-correct : ∀ s s' e → (δₐ s e ≡ just s' → s =[ e ]⇒ s') × (s =[ e ]⇒ s' → δₐ s e ≡ just s')
  app-step-correct s s' e = app-step-correctˡ s s' e , app-step-correctʳ s s' e
  
  _-[_]→_ = step-R {_=[_]⇒_ = _=[_]⇒_}


  -- parameterizing our state
  State = LState RawMsg AppEvent AppState
  
  
  
