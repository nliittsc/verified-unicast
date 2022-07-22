module Machine.Step where

open import Data.List
open import Data.List.Properties
open import Data.List.Membership.Propositional
open import Data.Nat using (ℕ)
open import Data.Product
open import Level
open import Machine.Core
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟨_⟩)
open ≡-Reasoning


open Msg public

private
  variable
    a b c ℓ : Level

{- Setting up some neccesary abstractions here -}

BinRel : Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ suc ℓ)
BinRel A B ℓ = A → B → Set ℓ

Relation : Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
Relation A ℓ = BinRel A A ℓ

TriRel : Set a → Set b → Set c → (ℓ : Level) → Set (a ⊔ b ⊔ c ⊔ suc ℓ)
TriRel A B C ℓ = A → B → C → Set ℓ

LabeledRel : Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ suc ℓ)
LabeledRel A B ℓ = TriRel A B A ℓ


---------- Unlabled Transition Relation ----------


-- Define the abstract multi-step (unlabled) transition relation
data multi {X : Set a} (R : Relation X (suc a)) : Relation X (suc a) where
  multi-refl : ∀ (x : X) → multi R x x
  multi-step : ∀ (x y z : X) → R x y → multi R y z → multi R x z

-- We can replace a single step with a "multi"-step
one-step-thm : ∀{X : Set a} (R : Relation X (suc a)) (x y : X) → R x y → (multi R) x y
one-step-thm R x y Rxy = multi-step x y y Rxy (multi-refl y)

-- the mult-step relation is transitive
multi-trans : ∀{X : Set a} (R : Relation X (suc a)) (x y z : X) → multi R x y → multi R y z → multi R x z
multi-trans R x .x z (multi-refl .x) R⋆yz = R⋆yz
multi-trans R x y₁ z (multi-step .x y .y₁ Rxy R⋆yy₁) R⋆yz = multi-step x y z Rxy (multi-trans R y y₁ z R⋆yy₁ R⋆yz)


---------- Labeled Transition Relation ----------



{- Define the abstract multi-step (labeled) transition relation.
   Sequences of actions are contained in lists -}
data labeled-multi {X : Set a} {A : Set b} (R : LabeledRel X A ℓ) : LabeledRel X (List A) (a ⊔ b ⊔ ℓ) where
  multi-refl : ∀(x : X) → labeled-multi R x [] x
  multi-step : ∀(x y z : X) (α : A) (ω : List A) → R x α y → labeled-multi R y ω z →
               labeled-multi R x (α ∷ ω) z

-- Analagous to `one-step-thm` but with sequences
labeled-one-step-thm : ∀{X : Set a} {A : Set b} (R : LabeledRel X A (suc (a ⊔ b))) (x y : X) (α : A) →
                       R x α y → labeled-multi R x [ α ] y
labeled-one-step-thm R x y α Rxαy = multi-step x y y α [] Rxαy (multi-refl y)


-- Not sure if needed...
labeled-multi-refl-lemma : ∀{X : Set a} {A : Set b} (R : LabeledRel X A (suc (a ⊔ b))) (x y : X) (ω : List A) →
                          labeled-multi R x ω y → labeled-multi R x (ω ++ []) y
labeled-multi-refl-lemma R x y ω R⋆xωy = subst (λ l → labeled-multi R x l y) (sym (++-identityʳ ω)) R⋆xωy


-- Analagous to `multi-trans`, but with labeled sequences
labeled-multi-trans : ∀{X : Set a} {A : Set b} (R : LabeledRel X A (suc (a ⊔ b))) (x y z : X) (ω₁ ω₂ : List A) →
                      labeled-multi R x ω₁ y → labeled-multi R y ω₂ z → labeled-multi R x (ω₁ ++ ω₂) z
labeled-multi-trans R x .x z .[] ω₂ (multi-refl .x) R⋆yω₂z = R⋆yω₂z
labeled-multi-trans R x y z .(α ∷ ω) ω₂ (multi-step .x y₁ .y α ω x₁ R⋆xω₁y) R⋆yω₂z = proof
  where
    proof : labeled-multi R x (α ∷ ω ++ ω₂) z
    proof = let ind-step = (labeled-multi-trans R y₁ y z ω ω₂ R⋆xω₁y R⋆yω₂z)
            in  multi-step x y₁ z α (ω ++ ω₂) x₁ ind-step


---------- Trace Theory ----------

-- Predicate that describes whether a sequence ω is a trace of the (refl-tran closure of the) relation R
traces : ∀{X : Set a} {A : Set b} → (R : LabeledRel X A ℓ) → (List A) → X → Set (a ⊔ b ⊔ ℓ)
traces R ω s = ∃ λ s' → labeled-multi R s ω s'



{- TRANSITION STATES -}

{- TODO: Add an event type which is the sum of consisting of message sends, receives, and
         other actions (such as get, post, etc) and modify process history to accept it

   TODO: Specialize the labeled transition relation to a transition on the process state
         called `LState` below. Try to keep transitions sufficiently general to allow
         reuse in different protocols

   TODO: Add a "local causal ordering" safety predicate on the LState below, test on some examples
         Note: This can maybe be written as a decision procedure

   TODO: Cook up a trivial protocol which has causal safety in terms of a transition system to test
         if specification makes sense
-} 


-- Generalized event type. The type `E` is an event that depends on the protocol
-- TODO: Should events contain their causal histories for dependency tracking?
--       This would allow a sort of general specification protocol, but not sure
--       how pragmatic it would be
data Event (A E : Set) : Set where
  send⟨_⟩ : Msg A → Event A E
  recv⟨_⟩ : Msg A → Event A E
  evt⟨_⟩    : E → Event A E


{- The generalized local state of a process. Has a process ID, a log containing
   a list of events that have happened, and an application-dependent piece of
   state (e.g., a delay queue, or input-output buffers)
-}
record LState (A E S : Set) : Set where
  constructor ⟨_﹐_﹐_⟩
  field
    pid   : Pid
    log   : List (Event A E)
    state : S


{- Defining Mattern's notion of _~_ to mean "happens on same process".
   Only applies to sends and receives. -}
data same-proc {A E : Set} : Event A E → Event A E → Set where
  two-sends : ∀{m m' : Msg A} → sender m ≡ sender m' → same-proc send⟨ m ⟩ send⟨ m' ⟩
  two-recvs : ∀{m m' : Msg A} → receiver m ≡ receiver m' → same-proc recv⟨ m ⟩ recv⟨ m' ⟩

{- Building the machinery for (local) causal ordering?
   Without causal dependency tracking, no way to know if the local state obeys causal
   delivery. So each event needs some history, or an approximation of that history...

   Feels like we need a theorem shaped like:
   "p₁ sends a message m to p₂ ⇔ ack/secret received..."

   Is there a way to track causal dependencies without maintaining extra state in
   the event or message datatype? Jonathan's work?
-}



{- Given a protocol-dependent event type (and state), and a way to transition
   the protocol-dependent state, transition the generalized local state by
   updating the history, and allowing the state to take a step
-}

-- Just a shorthand for the transition relation type
TSystem : Set → Set → Set → Set₂
TSystem A E S = LabeledRel (LState A E S) (Event A E) (suc 0ℓ)

infix 10 _-[_]→_

-- A local state transition system
data _-[_]→_ {A E S : Set}
             {_=⟨_⟩⇒_ : S → Event A E → S → Set}
             : TSystem A E S where

  -- If an event changes a local piece of state, change
  -- the state and update the history to include that event
  lstep : ∀{i h s s' α} → s =⟨ α ⟩⇒ s' →
          ⟨ i ﹐ h ﹐ s ⟩ -[ α ]→ ⟨ i ﹐ (α ∷ h) ﹐ s' ⟩

-- Possible lemma: ls -[ α ]→ ls' ⇔ history ls ⊂ history ls'

open import Data.Vec as V hiding (_++_)
open import Data.Fin as F hiding (suc)

-- Assuming some transition system
module SystemStep (n : ℕ) (A E S : Set) (_=⟨_⟩⇒_ : S → Event A E → S → Set) where

  _-⟨_⟩→_ : TSystem A E S
  _-⟨_⟩→_ = _-[_]→_ {A} {E} {S} {_=⟨_⟩⇒_}

  Process = LState A E S
  

  -- parameterized by number of states, message type, event type, state type
  -- System : ℕ → Set → Set → Set → Set₁
  System = V.Vec (LState A E S) n

  Action = Event A E
  
  SystemLTS = LabeledRel System Action (suc 0ℓ)

  -- Defines the system-wide transition system in terms of the local ones
  data _-[_]⇝_ : SystemLTS where

    {- If the process p at position i takes a step to p', the system
       takes a step to replace p with p' -}
    step : ∀{α : Action} {p p' : Process} {Π : System} {i : F.Fin n} →
           Π [ i ]= p → 
           p -⟨ α ⟩→ p' →
           Π -[ α ]⇝ (Π [ i ]≔ p')

  -- The reflexive-transitive closure
  _-[_]⇝⋆_ = labeled-multi _-[_]⇝_

  postulate
    -- TODO : Define this happens-before properly on the (linearization of?) events
    _≺hb_ : Event A E → Event A E → Set

    -- TODO: make this a module parameter somehow
    start-state : System → Set

  system-trace = traces _-[_]⇝_

  -- An execution is a system paired with a sequence of past actions
  Execution = System × List Action


  {- Important note: A "system trace" is a predicate which tells us if
     a sequence of actions will _lead to_ a valid system state from an
     _initial_ state. It is a subset of all lists of actions.

     A "well-formed" execution is a predicate that tells us if actions
     and a system are mutually compatible. They should be subtly different
  -}

  -- wf-exe : Execution → Set₁
  -- wf-exe (Π , ω) = {!!}

  {- Defining an operational version of "happens-before".
     Essentially happens-before but on a linearization.
     Should actually be decidable if comparing message
     types is decidable.

     TODO: Should there be a lemma relating this to traditional
           happens before or causal histories?

     FIXME: Should possible to define this more concisely with just
            wf-exe (Π , ω) and ω₁ ++ ω₂ ≡ ω since wf-exe "contains"
            information on the transition system
  -}

  -- Something like an "execution order"
  -- FIXME: Is this definition correct?
  data _≺[_]_ : Action → List Action × System → Action → Set₁ where
    exe-ord : ∀{e₁ e₂ ω Π₀ } ω₁ ω₂ → system-trace ω Π₀ →
              start-state Π₀ →
              e₁ ∈ ω₁ → e₂ ∈ ω₂ →
              ω₁ ++ ω₂ ≡ ω →
              e₁ ≺[ ω , Π₀ ] e₂

  -- Mattern's "happens on the same process". Only valid for two sends/two recvs
  _~_ = same-proc {A} {E}

  -- A predicate for causal-ordering.
  data CausallySafe (Π₀ : System) : Set₂ where
    co : ∀(ω : List (Event A E)) (m m' : Msg A) → system-trace ω Π₀ →
         send⟨ m ⟩ ∈ ω → send⟨ m' ⟩ ∈ ω  → recv⟨ m ⟩ ∈ ω → recv⟨ m' ⟩ ∈ ω →
         send⟨ m ⟩ ~ send⟨ m' ⟩ → recv⟨ m ⟩ ~ recv⟨ m' ⟩ →
         send⟨ m ⟩ ≺[ ω , Π₀ ] send⟨ m' ⟩ → recv⟨ m ⟩ ≺[ ω , Π₀ ] recv⟨ m' ⟩ →
         CausallySafe Π₀
