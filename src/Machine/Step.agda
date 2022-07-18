module Machine.Step where

open import Data.List
open import Data.List.Properties
open import Data.Nat
open import Data.Product
open import Machine.Core
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟨_⟩)
open ≡-Reasoning

{- Setting up some neccesary abstractions here -}

-- FIXME : Universe levels are messed up. Need to be polymorphic over
-- levels so that system-wide abstractions can be defined

BinRel : Set → Set → Set₁
BinRel A B = A → B → Set

Relation : Set → Set₁
Relation A = BinRel A A

TriRel : Set → Set → Set → Set₁
TriRel A B C = A → B → C → Set

LabeledRel : Set → Set → Set₁
LabeledRel A B = TriRel A B A


---------- Unlabled Transition Relation ----------


-- Define the abstract multi-step (unlabled) transition relation
data multi {X : Set} (R : Relation X) : Relation X where
  multi-refl : ∀ (x : X) → multi R x x
  multi-step : ∀ (x y z : X) → R x y → multi R y z → multi R x z

-- We can replace a single step with a "multi"-step
one-step-thm : ∀{X : Set} (R : Relation X) (x y : X) → R x y → (multi R) x y
one-step-thm R x y Rxy = multi-step x y y Rxy (multi-refl y)

-- the mult-step relation is transitive
multi-trans : ∀{X : Set} (R : Relation X) (x y z : X) → multi R x y → multi R y z → multi R x z
multi-trans R x .x z (multi-refl .x) R⋆yz = R⋆yz
multi-trans R x y₁ z (multi-step .x y .y₁ Rxy R⋆yy₁) R⋆yz = multi-step x y z Rxy (multi-trans R y y₁ z R⋆yy₁ R⋆yz)


---------- Labeled Transition Relation ----------



{- Define the abstract multi-step (labeled) transition relation.
   Sequences of actions are contained in lists -}
data labeled-multi {X A : Set} (R : LabeledRel X A) : LabeledRel X (List A) where
  multi-refl : ∀(x : X) → labeled-multi R x [] x
  multi-step : ∀(x y z : X) (α : A) (ω : List A) → R x α y → labeled-multi R y ω z →
               labeled-multi R x (α ∷ ω) z

-- Analagous to `one-step-thm` but with sequences
labeled-one-step-thm : ∀{X A : Set} (R : LabeledRel X A) (x y : X) (α : A) →
                       R x α y → labeled-multi R x [ α ] y
labeled-one-step-thm R x y α Rxαy = multi-step x y y α [] Rxαy (multi-refl y)


-- Not sure if needed...
labeled-multi-refl-lemma : ∀{X A : Set} (R : LabeledRel X A) (x y : X) (ω : List A) →
                          labeled-multi R x ω y → labeled-multi R x (ω ++ []) y
labeled-multi-refl-lemma R x y ω R⋆xωy = subst (λ l → labeled-multi R x l y) (sym (++-identityʳ ω)) R⋆xωy


-- Analagous to `multi-trans`, but with labeled sequences
labeled-multi-trans : ∀{X A : Set} (R : LabeledRel X A) (x y z : X) (ω₁ ω₂ : List A) →
                      labeled-multi R x ω₁ y → labeled-multi R y ω₂ z → labeled-multi R x (ω₁ ++ ω₂) z
labeled-multi-trans R x .x z .[] ω₂ (multi-refl .x) R⋆yω₂z = R⋆yω₂z
labeled-multi-trans R x y z .(α ∷ ω) ω₂ (multi-step .x y₁ .y α ω x₁ R⋆xω₁y) R⋆yω₂z = proof
  where
    proof : labeled-multi R x (α ∷ ω ++ ω₂) z
    proof = let ind-step = (labeled-multi-trans R y₁ y z ω ω₂ R⋆xω₁y R⋆yω₂z)
            in  multi-step x y₁ z α (ω ++ ω₂) x₁ ind-step


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
  send⟨_,_⟩ : Msg A → Event A E
  recv⟨_,_⟩ : Msg A → Event A E
  evt⟨_⟩    : E → Event A E


-- The generalized local state of a process
record LState (A E S : Set) : Set₁ where
  constructor ⟨_﹐_﹐_⟩
  field
    pid     : Pid
    history : List (Event A E)
    state   : S


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
TSystem A E S = LState A E S → Event A E → LState A E S → Set₁

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

open import Data.Vec as V
open import Data.Fin as F

-- Assuming some transition system
module SystemStep (n : ℕ) (A E S : Set) (_=⟨_⟩⇒_ : S → Event A E → S → Set) where

  _-⟨_⟩→_ : TSystem A E S
  _-⟨_⟩→_ = _-[_]→_ {A} {E} {S} {_=⟨_⟩⇒_}

  Process = LState A E S

  -- parameterized by number of states, message type, event type, state type
  -- System : ℕ → Set → Set → Set → Set₁
  System = V.Vec (LState A E S) n

  Action = Event A E
  
  -- LTS : ℕ → Set → Set → Set → Set₂
  LTS = System → Action → System → Set

  -- Defines the system-wide transition system in terms of the local ones
  data _-[_]⟿_ : System → Action → System → Set where

    {- If the process p at position i takes a step to p', the system
       takes a step to replace p with p' -}
    step : ∀{α : Action} {p p' : Process} {Π : System} {i : F.Fin n} →
           Π [ i ]= p → 
           p -⟨ α ⟩→ p' →
           Π -[ α ]⟿ (Π [ i ]≔ p')

  -- The reflexive-transitive closure
  _-[_]⟿⋆_ = labeled-multi {! _-[_]⟿_!}
