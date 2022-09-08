open import Data.Empty
open import Data.Fin
open import Data.Fin.Properties
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.Maybe
open import Data.Nat as ℕ hiding (_≟_)
open import Data.Product
open import Data.Sum
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟨_⟩)
open ≡-Reasoning
open import Relation.Nullary

module Abstractions.Network (num-site : ℕ)
                            (LocalState : Set)
                            (Msg : Set)
                            (δ : LocalState → List Msg → LocalState × List (Fin num-site × Msg))
                            (init-state : LocalState)
                            where
infixl 10 _[_←_]
infixl 5 _⟿⟨_⟩_

Pid = Fin num-site

-- Configuration/map update
_[_←_] : ∀{A : Set} → (Pid → A) → Pid → A → (Pid → A)
(c [ i ← cᵢ ]) j with i ≟ j
... | yes p = cᵢ
... | no ¬p = c j

-- bᵢⱼ : Buffer represents messages from sent
-- from i to j, but not yet delivered
record Buffer : Set where
  constructor buf
  field
    state : List Msg

open Buffer public

-- A configuration is the vector of local state and in-flight messages
Config = Pid → LocalState × (Pid → Buffer)

-- Given a message and destination we can update a buffer
enq-buffer : Pid × Msg → (Pid → Buffer) → (Pid → Buffer)
enq-buffer (j , m) bᵢ j′ with j ≟ j′
... | yes _ = let s = state (bᵢ j) in record (bᵢ j) { state = s ++ [ m ] }
... | no  _ = bᵢ j′

-- Removes a message from the buffer, while updating it
deq-buffer : Pid → (Pid → Buffer) → (Pid → Buffer) × Maybe Msg
deq-buffer j bᵢ with state (bᵢ j)
... | [] = bᵢ , nothing
... | (m ∷ msgs) = bᵢ [ j ← bᵢⱼ ] , just m
  where
    bᵢⱼ = record (bᵢ j) { state = msgs }


-- Two proofs of correctness of the update
buffer-correct₁ : (j : Pid) (m : Msg) (bᵢ : Pid → Buffer) → state (bᵢ j) ≡ [] → state (enq-buffer (j , m) bᵢ j) ≡ [ m ]
buffer-correct₁ j m bᵢ eq-prf with j ≟ j
... | yes p = subst (λ z → z ++ [ m ] ≡ [ m ]) (sym eq-prf) refl
... | no ¬p = ⊥-elim (¬p refl)

buffer-correct₂ : (j j′ : Pid) (m : Msg) (bᵢ : Pid → Buffer) → state (bᵢ j) ≡ [] → ¬ j′ ≡ j →
                  state (enq-buffer (j′ , m) bᵢ j) ≡ []
buffer-correct₂ j j′ m bᵢ eq-prf ¬j′≡j with j′ ≟ j
... | yes p = ⊥-elim (¬j′≡j p)
... | no ¬p = eq-prf

-- Now it's easy to update a buffer with a list of messages
merge-buffer : List (Pid × Msg) → (Pid → Buffer) → (Pid → Buffer)
merge-buffer [] bᵢ = bᵢ
merge-buffer (pckt ∷ pckts) bᵢ = merge-buffer pckts (enq-buffer pckt bᵢ)

-- transition function stuff for buffers
data BAction : Set where
  deq : Pid → BAction
  enq : List (Pid × Msg) → BAction

-- We have a way of updating buffers now
upd-buffer : (Pid → Buffer) → BAction → (Pid → Buffer) × Maybe Msg
upd-buffer bᵢ (deq j) = deq-buffer j bᵢ
upd-buffer bᵢ (enq msgs) = merge-buffer msgs bᵢ , nothing

data LAction : Set where
  τ    : LAction
  send : List (Pid × Msg) → LAction
  recv : List Msg → LAction
  deliv : Msg → Pid → LAction


-- shorthand
LConfig = LocalState × (Pid → Buffer)

-- Local process steps
data _⦂_-[_]→_ (i : Pid) : LConfig → LAction → LConfig → Set where
  -- silent computation event, no messages consumed
  compu-step : ∀ s s′ bᵢ →
               δ s [] ≡ (s′ , []) →
               i ⦂ (s , bᵢ) -[ τ ]→ (s′ , bᵢ)

  -- send computation event, no messages consumed
  send-step : ∀ s s′ bᵢ msgs-to-send →
         δ s [] ≡ (s′ , msgs-to-send) →
         let bᵢ′ = proj₁ (upd-buffer bᵢ (enq msgs-to-send))
         in i ⦂ (s , bᵢ) -[ send msgs-to-send ]→  (s′ , bᵢ′)

  -- a local receive event, at least one message consumed
  recv-step : ∀ s s′ bᵢ m msgs msgs-to-send →
               δ s (m ∷ msgs) ≡ (s′ , msgs-to-send) →
               let bᵢ′ = proj₁ (upd-buffer bᵢ (enq msgs-to-send))
               in i ⦂ (s , bᵢ) -[ recv (m ∷ msgs) ]→ (s′ , bᵢ′)

  -- some other process consumes from our output buffer
  deliv-step : ∀ s j bᵢ m →
               just m ≡ proj₂ (upd-buffer bᵢ (deq j)) →
               let bᵢ′ = proj₁ (upd-buffer bᵢ (deq j))
               in i ⦂ (s , bᵢ) -[ deliv m j ]→ (s , bᵢ′)

data Action : Set where
  τ : Pid → Action
  deliv : Msg → Pid → Pid → Action
  send : List (Pid × Msg) → Pid → Action

-- Configuration step. Seems to have FIFO order enforced
data _⟿⟨_⟩_ : Config → Action → Config → Set where
  compu-step : ∀ i c cᵢ′ →
               i ⦂ (c i) -[ τ ]→ cᵢ′ →
               c ⟿⟨ τ i ⟩ c [ i ← cᵢ′ ]

  send-step : ∀ i c cᵢ′ msgs →
              i ⦂ (c i) -[ send msgs ]→ cᵢ′ →
              c ⟿⟨ send msgs i ⟩ c [ i ← cᵢ′ ]

  deliv-step : ∀ i j c cᵢ cⱼ m →
               i ⦂ (c i) -[ deliv m j ]→ cᵢ →
               j ⦂ (c j) -[ recv [ m ] ]→ cⱼ →
               c ⟿⟨ deliv m i j ⟩ c [ i ← cᵢ ] [ j ← cⱼ ]

-- Defining an execution order from a starting state
data _⟿⋆⟨_⟩_ : Config → List Action → Config → Set where
  refl : ∀ c → c ⟿⋆⟨ [] ⟩ c
  iter : ∀ c₀ α A c c′ →
          c₀ ⟿⟨ α ⟩ c′ →
          c′ ⟿⋆⟨ A ⟩ c →
          c₀ ⟿⋆⟨ α ∷ A ⟩ c

-- A definition of "preceding"
_≺[_]_ : ∀{A : Set} → A → List A → A → Set
a ≺[ αs ] b = ∃₂ λ xs ys → (αs ≡ xs ++ ys × a ∈ xs × b ∈ ys)

-- An initial configuration
Init : Fin num-site → Fin num-site → Config → Set
Init i j c = proj₂ (c i) j ≡ buf []

deq-lemma : ∀ i j c → Init i j c → proj₂ (deq-buffer j (proj₂ (c i))) ≡ nothing
deq-lemma i j c init-c with proj₂ (c i) j | init-c
... | buf .[] | refl = refl

¬just-x≡nothing : ∀{A : Set} {x : A} → ¬ just x ≡ nothing
¬just-x≡nothing ()

α₁≺[L]α₂⇒α₁[α::L]α₂ : ∀{A : Set} {α₁ α₂ L} (α′ : A) → α₁ ≺[ L ] α₂ → α₁ ≺[ α′ ∷ L ] α₂
α₁≺[L]α₂⇒α₁[α::L]α₂ α′ (xs , ys , L≡xs++ys , α₁∈xs , α₂∈ys) = α′ ∷ xs , (ys , cong (_∷_ α′) L≡xs++ys , (there α₁∈xs , α₂∈ys))

-- TODO: Finish proving this correctness condition for the model
send≺deliv : ∀ i j m c c′ A →
             Init i j c →
             c ⟿⋆⟨ A ⟩ c′ →
             send [ (j , m) ] i ∈ A →
             deliv m i j ∈ A →
             send [ (j , m) ] i ≺[ A ] deliv m i j

-- deliv and send cant both be the first operation
send≺deliv i j m c c′ .(send [ (j , m) ] i ∷ _)  init-c c⟿⋆c′ (here refl) (here ())

-- the first operation is send, so the proof is trivial
send≺deliv i j m c c′ .(send [ (j , m) ] i ∷ xs) init-c c⟿⋆c′ p@(here {xs = xs} refl) (there deliv∈A) = prf
  where
    prf = [ send [ (j , m) ] i ] , (xs , refl , (here refl , deliv∈A))

-- A deliver happens before a send, which is impossible
send≺deliv i j m c c′ _ init-c (iter _ _ _ _ _ (deliv-step _ _ _ _ _ _ (deliv-step _ _ _ _ x) x₁) _) (there send∈A) (here refl) = prf
  where
    prf = ⊥-elim (¬just-x≡nothing (trans x (deq-lemma i j c init-c)))

-- Internal computation steps do not affect buffers, so its still an "initial" configuration
send≺deliv i j m c c′ (τ k ∷ A) init-c (iter .c .(τ k) A .c′ c₁ x c₁⟿⋆c′) (there send∈A) (there deliv∈A) = {!!}

-- Delivering somewhere else should allow us to proceed by induction. `Deliv i j m` can't happen by hypothesis.
send≺deliv i j m c c′ (deliv m′ i′ j′ ∷ A) init-c (iter _ _ A _ _ (deliv-step _ _ _ cᵢ cⱼ _ (deliv-step _ _ _ _ x) x₁) c₁⟿⋆c′) (there send∈A) (there deliv∈A) with i ≟ i′ | j ≟ j′
... | yes refl | yes refl = ⊥-elim (¬just-x≡nothing (trans x (deq-lemma i j c init-c)))
... | no ¬i≡i′ | yes refl = {!!}
... | yes refl | no ¬j≡j′ = {!!}
... | no ¬i≡i′ | no ¬j≡j′ = α₁≺[L]α₂⇒α₁[α::L]α₂ _ prf
  where
    p : Init i j ( c [ i ← cᵢ ] [ j ← cⱼ ])
    p = {!!}
    prf = (send≺deliv i j m {!!} {!!} {!!} {!!} c₁⟿⋆c′ send∈A deliv∈A)

-- If the message sent is the same as `send [ j , m ] i`, then we are done. Otherwise they are not the same,
-- so we should be able to proceed by induction....
send≺deliv i j m c c′ (send l i′ ∷ A) init-c (iter _ _ A _ c₁ x c₁⟿⋆c′) (there send∈A) (there deliv∈A) = {!!}


causal-deliv : ∀ i j k m₁ m₂ c c′ A →
               Init i j c →
               c ⟿⋆⟨ A ⟩ c′ →
               send [ (j , m₁) ] i ∈ A →
               send [ (j , m₂) ] k ∈ A →
               send [ (j , m₁) ] i ≺[ A ] send [ (j , m₂) ] k →
               deliv m₁ i j ∈ A → deliv m₂ k j ∈ A →
               deliv m₁ i j ≺[ A ] deliv m₂ k j
causal-deliv = {!!}
