open import Data.Empty
open import Data.List as L hiding (lookup)
open import Data.List.Membership.Propositional
open import Data.List.Membership.DecPropositional hiding (_∈_; _∉_)
open import Data.List.Relation.Unary.Any
open import Data.Fin as F hiding (_≥_)
open import Data.Nat as ℕ
open import Data.Product
open import Data.Sum
open import Data.Vec hiding (updateAt; _++_; _∷_; [_]; filter)
open import Data.Vec.Functional hiding (_++_; _∷_)
open import Data.Vec.Functional.Properties
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟨_⟩)
open import Relation.Nullary
open import Relation.Nullary.Negation

module Protocols.Matrix.Proofs (RawMsg : Set)
                               (num-site : ℕ)
                               (ApplicationState : Set)
                               (stateStep : ApplicationState → RawMsg → ApplicationState)
                               (_≡?_ : (rm₁ rm₂ : RawMsg) → Dec (rm₁ ≡ rm₂))
                               (produceMsgs : ApplicationState → List (Fin num-site × RawMsg)) where

open import Protocols.Matrix.Implementation RawMsg num-site ApplicationState stateStep produceMsgs _≡?_
open import Protocols.Utils RawMsg num-site _≡?_
open Message public


data Action : Set where
  send : Packet → Action
  dlvr : Packet → Action


deliv-cond : Pid → Deliv → Sent → Set
deliv-cond i delivᵢ stₘ = ∀ k → delivᵢ k ≥ stₘ k i

-- Local state is the application state, the sent matrix, and deliv matrix
-- currently abstracting out the application state
LocalState = Sent × Deliv

-- The initial local state
ls₀ : LocalState
ls₀ = (λ i j → 0) , (λ j → 0)

-- These rules show how local state evolves according to send and deliver
data _⟶loc⟨_⟩_ : LocalState → Action → LocalState → Set where
  send-local : ∀ i j m sentᵢ sentᵢ′ delivᵢ → i ≡ sender m → j ≡ dest m →
               sentᵢ′ ≡ sendTick sentᵢ i j →
               (sentᵢ , delivᵢ) ⟶loc⟨ send (m , sentᵢ′) ⟩ (sentᵢ′ , delivᵢ)

  dlvr-local : ∀ i j m stₘ sentᵢ sentᵢ′ delivᵢ delivᵢ′ → j ≡ sender m → i ≡ dest m →
               deliv-cond i delivᵢ stₘ →
               delivᵢ′ ≡ delivTick delivᵢ j →
               sentᵢ′ ≡ sendTick sentᵢ j i →
               (sentᵢ , delivᵢ) ⟶loc⟨ dlvr (m , stₘ) ⟩ (sentᵢ′ ∨ stₘ , delivᵢ′)

⟶loc-determ : ∀ {x y z a} → x ⟶loc⟨ a ⟩ y → x ⟶loc⟨ a ⟩ z → y ≡ z
⟶loc-determ (send-local i j m sentᵢ sentᵢ′ delivᵢ x x₂ x₃) (send-local i₁ j₁ .m .sentᵢ .sentᵢ′ .delivᵢ x₁ x₄ x₅) = refl
⟶loc-determ (dlvr-local i j m stₘ sentᵢ sentᵢ′ delivᵢ delivᵢ′ refl refl x₃ refl refl) (dlvr-local i₁ j₁ _ _ _ sentᵢ′₁ _ delivᵢ′₁ refl refl x₇ refl refl) = refl


-- The communication medium is a matrix of out-going message channels
Channel = Vector (Vector (List Packet) num-site) num-site

-- The initial channel
chan₀ : Channel
chan₀ = λ i j → L.[]

-- Sending a packet appends it to the end of a channel
chan-send-upd : Channel → Pid → Pid → Packet → Channel
chan-send-upd chan i j pckt = updateAt i f chan
  where
    f = updateAt j (λ xs → xs ++ [ pckt ])

-- Delivering a packet removes it from the channel
chan-dlvr-upd : Channel → Pid → Pid → Packet → Channel
chan-dlvr-upd chan i j pckt = updateAt i f chan
  where
    f = updateAt j (λ xs → filter (λ x → ¬? (x ≡ₚ? pckt)) xs)
    
-- These rules show how the communication medium evolves according to send and deliver
data _⟶com⟨_⟩_ : Channel → Action → Channel → Set where
  send-chan : ∀ i j m stₘ chan → i ≡ sender m → j ≡ dest m →
              let chan′ = chan-send-upd chan i j (m , stₘ)
              in chan ⟶com⟨ send (m , stₘ) ⟩ chan′

  dlvr-chan : ∀ i j m stₘ chan → j ≡ sender m → i ≡ dest m →
              (m , stₘ) ∈ chan i j →
              let chan′ = chan-dlvr-upd chan j i (m , stₘ)
              in chan ⟶com⟨ dlvr (m , stₘ) ⟩ chan′

-- dhc-chan : ∀ {i j m stₘ chan chan′} → chan ⟶⟨ dlvr (m , stₘ) ⟩ chan′ →  

-- A system state is the communication medium and a cross product of local states
SysState = Channel × Vector LocalState num-site

-- retrieve the clock at a place in the system
_⦂_↦clock : SysState → Pid → Sent
(_ , v) ⦂ i ↦clock = proj₁ (v i)

-- retrieve the deliv vector in the system
_◅_↦deliv : SysState → Pid → Deliv
(_ , v) ◅ i ↦deliv = proj₂ (v i) 

-- The initial states of our system
x₀ : SysState
x₀ = chan₀ , λ i → ls₀ 

-- Steps in the system are just composed local steps
data _⟿⟨_⟩_ : SysState → Action → SysState → Set where
  send-step : ∀ {i pckt chan chan′ v vᵢ vᵢ′} →
              i ≡ sender (proj₁ pckt) →
              v i ≡ vᵢ →
              vᵢ ⟶loc⟨ send pckt ⟩ vᵢ′ →
              chan ⟶com⟨ send pckt ⟩ chan′ →
              (chan , v) ⟿⟨ send pckt ⟩ (chan′ , v [ i ← vᵢ′ ])

  dlvr-step : ∀ {i pckt chan chan′ v vᵢ vᵢ′} →
              i ≡ dest (proj₁ pckt) →
              v i ≡ vᵢ →
              vᵢ ⟶loc⟨ dlvr pckt ⟩ vᵢ′ →
              chan ⟶com⟨ dlvr pckt ⟩ chan′ →
              (chan , v) ⟿⟨ dlvr pckt ⟩ (chan′ , v [ i ← vᵢ′ ])

postulate
  -- these are true, but not sure if needed yet

  -- the rules are deterministic for a fixed action
  ⟿-determ : ∀ {x y z a} → x ⟿⟨ a ⟩ y → x ⟿⟨ a ⟩ z → y ≡ z
  -- below actually follows from determinism
  ⟿-succ : ∀ x a → (∃ λ x′ → x ⟿⟨ a ⟩ x′)


data multi {A B : Set} (R : A → B → A → Set) : A → List B → A → Set where
  multi-refl : ∀ {a} → multi R a L.[] a
  multi-iter : ∀ {a b a′ a″ ω} → R a b a′ → multi R a′ ω a″ → multi R a (b L.∷ ω) a″

-- This is transitive closure, but defined a different way
data comulti {A B : Set} (R : A → B → A → Set) : A → List B → A → Set where
  multi-refl : ∀{a} → comulti R a L.[] a
  multi-iter : ∀ {x b y z w} → comulti R x w y → R y b z → comulti R x (b ∷ w) z

-- If a step exists in our computation, we can partition the computation on that step
prefix-lemma : ∀{A B : Set} {x z : A} {a : B} {w R} →
               let R⋆ = comulti R in
               R⋆ x w z → a ∈ w →
               (∃ λ y → (∃₂ λ w₁ w₂ → R⋆ x (a ∷ w₁) y × R⋆ y w₂ z))
prefix-lemma {z = z} R⋆xwz (here refl) = z , _ , L.[] , R⋆xwz , multi-refl
prefix-lemma (multi-iter R⋆xwy Rybz) (there a∈w) with prefix-lemma R⋆xwy a∈w
... | t , l₁ , l₂ , R⋆xl₁t , R⋆tl₂y = t , l₁ , _ , R⋆xl₁t , multi-iter R⋆tl₂y Rybz

-- If a step exists in our computation, we can extract that step and its nearby states
∃step : ∀{A B : Set} {x z : A} {a : B} {w R} →
        let R⋆ = comulti R in
        R⋆ x w z → a ∈ w →
        (∃₂ λ (y₁ y₂ : A) → (∃₂ λ (w₁ w₂ : List B) → R⋆ x w₁ y₁ × R y₁ a y₂ × R⋆ y₂ w₂ z))
∃step (multi-iter R⋆xwy Ryaz) (here refl) = _ , _ , _ , _ , prf
  where
    prf = R⋆xwy , Ryaz , multi-refl
∃step (multi-iter R⋆xwy Rybz) (there a∈w) with ∃step R⋆xwy a∈w
... | y₁ , y₂ , w₁ , w₂ , R⋆xw₁y₁ , Ry₁ay₂ , R⋆y₂w₂z = _ , _ , _ , _ , prf
  where
    prf = R⋆xw₁y₁ , Ry₁ay₂ , multi-iter R⋆y₂w₂z Rybz

-- Reflexive transitive closure
_⟿⋆⟨_⟩_ = comulti _⟿⟨_⟩_


-- We need a way to say whether two events 'happen' on the same process
data _∼_ : Action → Action → Set where
  local-sends : ∀ {p p′} → sender (proj₁ p) ≡ sender (proj₁ p′) → send p ∼ send p′
  local-dlvrs : ∀ {p p′} → dest (proj₁ p) ≡ dest (proj₁ p′) → dlvr p ∼ dlvr p′
  send-dlvrs  : ∀ {p p′} → sender (proj₁ p) ≡ dest (proj₁ p′) → send p ∼ dlvr p′

-- TODO: prove the above relation is symmetric, transitive

-- List ordering; defining what it means for x to appear before y in a list
data _≺[_]_ {A : Set} : A → List A → A → Set where
  ≺-base : ∀ x y l → x ≺[ x ∷ y ∷ l ] y
  ≺-succ : ∀ {x y l} z → x ≺[ l ] y → x ≺[ z ∷ l ] y
  ≺-trans : ∀ {x y z l l′ l″} → l″ ≡ l ++ [ y ] ++ l′ → x ≺[ l ] y → y ≺[ y ∷ l′ ] z → x ≺[ l″ ] z

data _⊢_≾_ {A : Set} {x y : A} :  (w : List A) → (x ∈ w) → (y ∈ w) → Set where
  here-rule : ∀{w : List A} → (p : y ∈ w) → (x ∷ w) ⊢ here refl ≾ there p
  there-rule : ∀{z : A} {w : List A} → (p : x ∈ w) → (q : y ∈ w) → w ⊢ p ≾ q → (z ∷ w) ⊢ there p ≾ there q

-- A causal dependency relation.
data _⇒⟨_⟩_ : Action → List Action → Action → Set where
  ⇒-local : ∀ {a a′ w} {a∈w : a ∈ w} {a′∈w : a′ ∈ w} →  a ∼ a′ → w ⊢ a′∈w ≾ a∈w → a ⇒⟨ w ⟩ a′
  ⇒-cause : ∀ {p ω}  → send p ∈ ω → dlvr p ∈ ω → send p ⇒⟨ ω ⟩ dlvr p
  ⇒-trans : ∀ {a a′ a″ ω} → a ⇒⟨ ω ⟩ a′ → a′ ⇒⟨ ω ⟩ a″ → a ⇒⟨ ω ⟩ a″

postulate
  _≡a?_ : (a₁ a₂ : Action) → Dec (a₁ ≡ a₂)
  _∼?_  : (a₁ a₂ : Action) → Dec (a₁ ∼ a₂)

_∈ₐ?_ = _∈?_ _≡a?_

-- The relation is decidable
-- TODO: prove it
postulate
  _⇒?⟨_⟩_ : (a₁ : Action) → (w : List Action) → (a₂ : Action) → Dec (a₁ ⇒⟨ w ⟩ a₂)
-- a₁ ⇒?⟨ w ⟩ a₂ with a₁ ∈ₐ? w | a₂ ∈ₐ? w
-- ... | yes a₁∈w | yes a₂∈w = {!!}
-- ... | yes a₁∈w | no  a₂∉w = no {!!}
-- ... | no  a₁∉w | yes a₂∈w = {!!}
-- ... | no  a₁∉w | no  a₂∉w = {!!}

-- CO is shorthand for Causally Ordered
data CO : List Action → Set where
  emp : CO L.[]
  
-- If something happens-before in a list, it still happens-before in the extended list
hb-succ : ∀{a a₁ a₂ w} → a₁ ⇒⟨ w ⟩ a₂ → a₁ ⇒⟨ a ∷ w ⟩ a₂
hb-succ (⇒-local x x₁) = ⇒-local x (there-rule _ _ x₁)
hb-succ (⇒-cause x x₁) = ⇒-cause (there x) (there x₁)
hb-succ (⇒-trans a₁⇒x x⇒a₂) = ⇒-trans (hb-succ a₁⇒x) (hb-succ x⇒a₂)

postulate
  sendTick-correct  : ∀ (sent : Sent) i j → sent i j ℕ.≤ (sendTick sent i j) i j
  delivTick-correct : ∀ (deliv : Deliv) j → deliv j ℕ.≤ (delivTick deliv j) j
  monotonic₁ : ∀ {i x a x′} → x ⟿⟨ a ⟩ x′ → (x ⦂ i ↦clock) i ≼ (x′ ⦂ i ↦clock) i
  monotonic₂ : ∀ {i x a x′} → x ⟿⟨ a ⟩ x′ → (x ◅ i ↦deliv) ≼ (x ◅ i ↦deliv)



dlvr⇒deliverable : ∀ {x y} m stₘ → x ⟿⟨ dlvr (m , stₘ) ⟩ y →
                    let i = dest m
                    in deliv-cond i (x ◅ i ↦deliv) stₘ
dlvr⇒deliverable m stₘ (dlvr-step refl refl (dlvr-local _ j .m .stₘ _ sentᵢ′ _ delivᵢ′ refl refl x₂ x₄ x₅) x₃) k = x₂ k

-- If something was delivered in a trace, then we can produce the system state which delivered it
dlvr⇒∃deliverable : ∀ {x y w m stₘ} → x ⟿⋆⟨ w ⟩ y →
                    dlvr (m , stₘ) ∈ w →
                    let i = dest m
                    in ∃ λ x′ → deliv-cond i (x′ ◅ i ↦deliv) stₘ
dlvr⇒∃deliverable = {!!}

-- delivability is an invariant, actually
lemma₁ : ∀{m : Message}  {stₘ x a x′} → deliv-cond (dest m) (x ◅ dest m ↦deliv) stₘ →
         x ⟿⟨ a ⟩ x′ → deliv-cond (dest m) (x′ ◅ dest m ↦deliv) stₘ
lemma₁ d-con₁ x⟿ₐx′ k = {!!}

lemma₂ : ∀ {m₁ m₂ : Message} {stₘ₁ stₘ₂ ω} →
         send (m₁ , stₘ₁) ⇒⟨ ω ⟩ send (m₂ , stₘ₂) →
         let j = sender m₁
             i = dest m₁
         in stₘ₁ j i ℕ.≤ stₘ₂ j i

lemma₂ = {!!}


lemma₃ : ∀ {m stₘ p x ω} → dlvr (m , stₘ) ∼ dlvr p →  send (m , stₘ) ⇒⟨ ω ⟩ send p →
         dlvr p ∈ ω → deliv-cond (dest m) (x ◅ dest m ↦deliv) stₘ

lemma₃ = {!!}


-- distinct elements are totally ordered in a list
≢⇒total : ∀ {A : Set} {x y : A} {w} → (p : x ∈ w) → (q : y ∈ w) → ¬ (x ≡ y) → (w ⊢ p ≾ q) ⊎ (w ⊢ q ≾ p)
≢⇒total (here px) (here refl) x≢y = contradiction px x≢y
≢⇒total (here refl) (there q) x≢y = inj₁ (here-rule q)
≢⇒total (there p) (here refl) x≢y = inj₂ (here-rule p)
≢⇒total (there p) (there q) x≢y with ≢⇒total p q x≢y
... | inj₁ prf₁ = inj₁ (there-rule p q prf₁)
... | inj₂ prf₂ = inj₂ (there-rule q p prf₂)


-- From the initial state, the first action can't be a deliver
no-init-dlvrs : ∀ {p x} → x₀ ⟿⟨ dlvr p ⟩ x → ⊥
no-init-dlvrs (dlvr-step refl refl x₂ (dlvr-chan i j m stₘ .chan₀ x x₁ ()))

-- no-init-dlvrs⋆ : ∀ {p x w} → x₀ ⟿⋆⟨ dlvr p ∷ w ⟩ x → ⊥
-- no-init-dlvrs⋆ (multi-iter x x₀⟿⋆) = no-init-dlvrs x

send≢dlvr : ∀{pckt} → ¬ (send pckt ≡ dlvr pckt)
send≢dlvr ()

postulate
  ≡pckt? : (pckt₁ pckt₂ : Packet) → Dec (pckt₁ ≡ pckt₂)

data Distinct {A : Set} : List A → Set where
  emp  : Distinct L.[]
  _∷_ : ∀{x xs} → x ∉ xs → Distinct xs → Distinct (x ∷ xs)



corollary5 : ∀{m₁ m₂ stₘ₁ stₘ₂ w x} →
            x₀ ⟿⋆⟨ w ⟩ x → send (m₁ , stₘ₁) ⇒⟨ w ⟩ send (m₂ , stₘ₂) →
            let j = sender m₁
                i = dest m₁
             in stₘ₁ j i ℕ.< stₘ₂ j i

corollary5 x₀⟿⋆y s₁⇒s₂ = {!!}


dhc-lemma₁ : ∀{pckt w x} → Distinct w → x₀ ⟿⋆⟨ w ⟩ x → dlvr pckt ∈ w → send pckt ∈ w
dhc-lemma₁ dw (multi-iter multi-refl x) (here refl) = ⊥-elim (no-init-dlvrs x)
dhc-lemma₁ {pckt} dw (multi-iter (multi-iter {b = send pckt′} multi-refl x₁) x) (here refl) with ≡pckt? pckt pckt′
... | yes refl = there (here refl)
dhc-lemma₁ {pckt} dw (multi-iter (multi-iter {_} {.(send _)} multi-refl x₁) (dlvr-step x x₂ x₃ x₄)) (here refl) | no ¬p = {!!}
dhc-lemma₁ dw (multi-iter (multi-iter {b = dlvr x₂} multi-refl x₁) x) (here refl) = ⊥-elim (no-init-dlvrs x₁)
dhc-lemma₁ dw (multi-iter (multi-iter {b = b} (multi-iter x₀⟿⋆x x₂) x₁) x) (here refl) = {!!}
dhc-lemma₁ (x₁ ∷ dw) (multi-iter x₀⟿⋆x x) (there d∈w) = there (dhc-lemma₁ dw x₀⟿⋆x d∈w)

dhc-lemma : ∀{pckt w x} {s∈w : send pckt ∈ w} {d∈w : dlvr pckt ∈ w} → Distinct w → x₀ ⟿⋆⟨ w ⟩ x → w ⊢ s∈w ≾ d∈w → ⊥
dhc-lemma (s∉w ∷ dw) (multi-iter x₀⟿⋆y y⟿x) (here-rule d∈w) = contradiction (dhc-lemma₁ dw x₀⟿⋆y d∈w) s∉w
dhc-lemma (x₁ ∷ dw) (multi-iter x₀⟿⋆x x) (there-rule p q w⊢s∈w≾d∈w) = dhc-lemma dw x₀⟿⋆x w⊢s∈w≾d∈w

-- dhc-lemma : ∀{pckt w x} {s∈w : send pckt ∈ w} {d∈w : dlvr pckt ∈ w} → Distinct w → x₀ ⟿⋆⟨ w ⟩ x → w ⊢ d∈w ≾ s∈w → ⊥
-- Delivers never happen first, so these two cases are impossible
-- dhc-lemma _ x (here-rule p) = ⊥-elim (no-init-dlvrs⋆ x)
-- dhc-lemma dw (multi-iter t@(dlvr-step x x₃ x₄ x₅) x₂) (there-rule p q x₁) = ⊥-elim (no-init-dlvrs t)

-- -- TODO: Need to prove that if the first step is some send, but a deliver occurs before a send anyway, then we get false
-- dhc-lemma {pckt} (s∉w ∷ dw) (multi-iter (send-step {pckt = pckt₁} refl refl (send-local i j m _ sentᵢ′ _ x x₁ x₂) chan₀⟶chan′) ⟿⋆x) (there-rule d∈w s∈w w⊢d≾s) = {!!}



-- The semantics guarantee sends happen before delivers
dlvrs-have-cause : ∀{pckt w x} → Distinct w → (s∈w : send pckt ∈ w) → (d∈w : dlvr pckt ∈ w) → x₀ ⟿⋆⟨ w ⟩ x → w ⊢ s∈w ≾ d∈w
dlvrs-have-cause = {!!}


-- dlvrs-have-cause _ (here refl) (there d∈w) x₀⟿x′ = here-rule d∈w
-- dlvrs-have-cause _ (there s∈w) (here refl) x₀⟿x′ = ⊥-elim (no-init-dlvrs⋆ x₀⟿x′)
-- dlvrs-have-cause dw (there s∈w) (there d∈w) x₀⟿x′ with ≢⇒total s∈w d∈w send≢dlvr
-- ... | inj₁ prf₁ = there-rule s∈w d∈w prf₁
-- ... | inj₂ prf₂ = ⊥-elim (dhc-lemma dw x₀⟿x′ (there-rule d∈w s∈w prf₂))

-- safety₁ : ∀ {p₁ m stₘ w x x x′} →
--            x₀ ⟿⋆⟨ w ⟩ x →
--            send p₁ ⇒⟨ w ⟩ send  (m , stₘ)→
--            dlvr p₁ ∼ dlvr (m , stₘ) →
--            dlvr p₁ ∉ w →
--            ¬ deliv-cond (dest m) (x ◅ dest m ↦deliv) stₘ →

-- data CausalChain (a : Action) : List Action → List Action → Set where
--   [-] : CausalChain a L.[] [ a ]
--   cause : ∀ {a′ xs ys} → CausalChain a (a′ ∷ xs) ( 
  



safety : ∀ {p₁ p₂ w x} →
           x₀ ⟿⋆⟨ w ⟩ x →
           send p₁ ⇒⟨ w ⟩ send p₂ →
           dlvr p₁ ∼ dlvr p₂ →
           dlvr p₁ ∉ w →
           ¬ (∃ λ y → x ⟿⟨ dlvr p₂ ⟩ y)
safety x₀⟿⋆x (⇒-local s₁∼s₂ s₂≾s₁) d₁∼d₂ d₁∉w (y , x⟿y) = {!!}
safety x₀⟿⋆x (⇒-trans s₁⇒s₂ s₁⇒s₃) d₁∼d₂ d₁∉w (y , x⟿y) = {!!}

correct₁ : ∀ {p₁ p₂ w x} →
           Distinct w →
           x₀ ⟿⋆⟨ w ⟩ x →
           send p₁ ⇒⟨ w ⟩ send p₂ →
           dlvr p₁ ∼ dlvr p₂ →
           dlvr p₁ ∈ w → dlvr p₂ ∈ w →
           dlvr p₁ ⇒⟨ w ⟩ dlvr p₂

-- This case should be impossible because I should be able to prove that _⇒⟨_⟩_ is irreflexive
correct₁ {p₁} {.p₁} {.(dlvr p₁ ∷ _)} (x ∷ dw) x₀⟿⋆x s₁⇒s₂ d₁∼d₂ (here refl) (here refl) = {!!}

-- This case should be impossible, because if the *last* thing we did was deliver m1, and deliver m2 is
-- in the trace, we have violated causality. This is the *hard* case
correct₁ {p₁} {p₂} {.(dlvr p₁ ∷ _)} dw x₀⟿⋆x s₁⇒s₂ d₁∼d₂ (here refl) (there d₂∈w) = {!!}

-- Easy
correct₁ {p₁} {p₂} {.(dlvr p₂ ∷ _)} dw x₀⟿⋆x s₁⇒s₂ d₁∼d₂ (there d₁∈w) (here refl) = ⇒-local d₁∼d₂ (here-rule d₁∈w)

-- If the last thing we did was send m2, we cannot have also delivered it. Should follow from "delivers have cause" lemmas
correct₁ {p₁} {p₂} {.(send p₂ ∷ _)} dw x₀⟿⋆x (⇒-local x (here-rule p)) d₁∼d₂ (there d₁∈w) (there d₂∈w) = {!!}

-- easy
correct₁ {p₁} {p₂} {.(_ ∷ _)} (x₂ ∷ dw) (multi-iter x₀⟿⋆y y⟿x) (⇒-local x (there-rule p q x₁)) d₁∼d₂ (there d₁∈w) (there d₂∈w) = prf
  where
    prf = hb-succ (correct₁ dw x₀⟿⋆y (⇒-local x x₁) d₁∼d₂ d₁∈w d₂∈w)

{-- transitive case. I think to solve this, case on the actions.
--   1. If the action is a send, we check if there was
        a delivery. If yes, we can use induction+transitivity to order them.
        If no delivery occured, then this case reduces to the "hard" case above
     2. If the action is a delivery, I have no idea at the moment
--}
correct₁ {p₁} {p₂} {.(_ ∷ _)} dw x₀⟿⋆x (⇒-trans s₁⇒s₂ s₁⇒s₃) d₁∼d₂ (there d₁∈w) (there d₂∈w) = {!!}


