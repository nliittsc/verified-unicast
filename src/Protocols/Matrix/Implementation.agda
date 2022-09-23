open import Data.Empty
open import Data.Fin as F hiding (_+_; _≥_; _≤_; _≤?_)
open import Data.Fin.Properties as F
open import Data.List hiding (lookup; merge; replicate; zipWith)
open import Data.Nat as ℕ
open import Data.Nat.Properties as ℕ
open import Data.Product
open import Data.Sum
-- open import Data.Vec hiding ([_]; _++_; init)
-- open import Data.Vec.Properties
-- open import Data.Vec.Relation.Binary.Pointwise.Extensional renaming (refl to pw-refl; sym to pw-sym; trans to pw-trans)
open import Data.Vec.Functional as V hiding (_++_) renaming ([] to ⟨⟩)
open import Data.Vec.Functional.Properties
open import Data.Vec.Functional.Relation.Binary.Pointwise
open import Data.Vec.Functional.Relation.Binary.Pointwise.Properties
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟨_⟩)
open import Relation.Nullary
open import Relation.Nullary.Implication
open import Relation.Nullary.Negation
open import Relation.Nullary.Product
open import Relation.Unary
open ≡-Reasoning

-- We make some assumptions on the underlying implementation
module Protocols.Matrix.Implementation (RawMsg : Set)
                                       (num-site : ℕ)
                                       (LocalState : Set)
                                       (stateStep : LocalState → RawMsg → LocalState)
                                       (produceMsgs : LocalState → List (Fin num-site × RawMsg))
                                       (_≡?_ : (rm₁ rm₂ : RawMsg) → Dec (rm₁ ≡ rm₂)) where

open import Protocols.Utils RawMsg num-site _≡?_
open Message public

Matrix : Set → ℕ → ℕ → Set
Matrix A m n = Vector (Vector A n) m

SqMatrix : Set → ℕ → Set
SqMatrix A n = Matrix A n n

-- retrieve the column of a matrix
_[-﹐_] : ∀{A : Set} {n m} → Matrix A m n → Fin n → Vector A m
_[-﹐_] {A} {n} {zero} x j = ⟨⟩
_[-﹐_] {A} {n} {suc m} f j = V.head f j V.∷ (V.tail f [-﹐ j ])

-- Map updates
infixl 10 _[_←_]
_[_←_] : ∀{A : Set} {n} → Vector A n → Fin n → A → Vector A n
v [ i ← x ] = updateAt i (λ _ → x) v

-- For assigning to the row-col in a matrix
_[_﹐_←_] : ∀{A : Set} {n m} → Matrix A m n → Fin m → Fin n → A → Matrix A m n
x [ i ﹐ j ← e ] =
  let row  = x i
      row′ = row [ j ← e ]
  in x [ i ← row′ ]
  
max : ℕ → ℕ → ℕ
max n m with n ≥? m
... | yes _ = n
... | no  _ = m

max-correctˡ : ∀ n m → n ≤ max n m
max-correctˡ n m with n ≥? m
... | yes n≥m = ℕ.≤-refl
... | no ¬n≥m with ℕ.≤-total n m
...    | inj₁ n≤m = n≤m
...    | inj₂ n≥m = ⊥-elim (¬n≥m n≥m)

max-correctʳ : ∀ n m → m ≤ max n m
max-correctʳ n m with n ≥? m
... | yes n≥m = n≥m
... | no ¬n≥m = ℕ.≤-refl


-- Defines whether a vector "dominates" another
infixl 10 _≼_
_≼_ = Pointwise _≤_

-- Vector domination is decidable
_≼?_ : ∀{n} → (u v : Vector ℕ n) → Dec (u ≼ v)
_≼?_ {n} u v = decidable ℕ._≤?_ u v


-- Merging two vectors, pointwise. A join operation
infixl 12 _⋄_
_⋄_ : ∀{n} → Vector ℕ n → Vector ℕ n → Vector ℕ n
u ⋄ v = zipWith max u v

-- Proving that our join operation works as intended
join-vec-correctˡ : ∀{n} → (x y : Vector ℕ n) → x ≼ x ⋄ y
join-vec-correctˡ x y i with y i ℕ.≤? x i
... | yes p = ℕ.≤-refl
... | no ¬p = ≰⇒≥ ¬p


join-vec-correctʳ : ∀{n} → (x y : Vector ℕ n) → y ≼ x ⋄ y
join-vec-correctʳ x y i with y i ℕ.≤? x i
... | yes p = p
... | no ¬p = ℕ.≤-refl

join-vec-correct : ∀{n} → (x y : Vector ℕ n) → (x ≼ x ⋄ y) × (y ≼ x ⋄ y)
join-vec-correct {n} x y = prfˡ , prfʳ
  where
    prfˡ = join-vec-correctˡ x y
    prfʳ = join-vec-correctʳ x y

-- Join two matrices
infixl 12 _∨_
_∨_ : ∀{n} → SqMatrix ℕ n → SqMatrix ℕ n → SqMatrix ℕ n
x ∨ y = zipWith (_⋄_) x y

{- Machinery for our server/process -}
Sent = SqMatrix ℕ num-site
Deliv = Vector ℕ num-site

-- Defines the state of our process
record State : Set where
  constructor st
  field
    pid   : Pid
    state : LocalState
    clock : Sent
    deliv : Deliv
    
open State public

-- A packet is a message with an attached clock
Packet = Message × Sent

-- We can decide between two packets. Postulating this because it's obvious but tedious
postulate
  _≡ₚ?_ : (p₁ p₂ : Packet) → Dec (p₁ ≡ p₂)


sendTick : Sent → Pid → Pid → Sent
sendTick sentᵢ i j = sentᵢ [ i ﹐ j ← (sentᵢ i j + 1) ]


delivTick : Deliv → Pid → Deliv
delivTick delivᵢ j = delivᵢ [ j ← delivᵢ j + 1 ]

-- -- -- First delivery condition
-- -- deliverable?₁ : (delivᵢ : Deliv) (stₘ : Sent) (i j : Pid) →
-- --                  Dec (lookup delivᵢ j + 1 ≡ stₘ [ j ﹐ i ])
-- -- deliverable?₁ delivᵢ stₘ i j with (lookup delivᵢ j + 1) ℕ.≟ stₘ [ j ﹐ i ]
-- -- ... | yes p = yes p
-- -- ... | no ¬p = no ¬p

-- -- -- Second delivery condition
-- -- deliverable?₂ : (delivᵢ : Deliv) (stₘ : Sent) (i j : Pid) →
-- --                 Dec (∀ k → ¬ k ≡ j → lookup delivᵢ k ≥ stₘ [ k ﹐ i ])
-- -- deliverable?₂ delivᵢ stₘ i j = all? (λ x → ¬? (x F.≟ j) →-dec lookup delivᵢ x ≥? (stₘ [ x ﹐ i ]))

-- -- -- The deliverability condition
-- -- Deliverable : State → Packet → Set
-- -- Deliverable s (m , stₘ) =
-- --   let i = pid s
-- --       j = dest m
-- --       delivᵢ = deliv s
-- --       cond₁ = lookup delivᵢ j + 1 ≡ stₘ [ j ﹐ i ]
-- --       cond₂ = ∀ k → ¬ k ≡ j → lookup delivᵢ k ≥ stₘ [ k ﹐ i ]
-- --       cond₃ = i ≡ j
-- --   in cond₁ × cond₂ × cond₃


-- -- -- The deliverability condition is decidable
-- -- deliverable? : (s : State) → (pckt : Packet) → Dec (Deliverable s pckt)
-- -- deliverable? (st i s sentᵢ delivᵢ)  (m , stₘ) = cond₁-dec ×-dec cond₂-dec ×-dec cond₃-dec
-- --   where
-- --     cond₁-dec = deliverable?₁ delivᵢ stₘ i (dest m)
-- --     cond₂-dec = deliverable?₂ delivᵢ stₘ i (dest m)
-- --     cond₃-dec = i F.≟ dest m

Deliverable : State → Packet → Set
Deliverable s (m , stₘ) =
  let i = pid s
      j = dest m
      delivᵢ = deliv s
      cond₁ = ∀ k → delivᵢ k ≥ stₘ k i
      cond₂ = i ≡ j
  in cond₁ × cond₂

deliverable? : (s : State) → (pckt : Packet) → Dec (Deliverable s pckt)
deliverable? (st i ls sentᵢ delivᵢ) (m , stₘ) = cond₁-dec ×-dec cond₂-dec
  where
    cond₁-dec = all? (λ k → delivᵢ k ≥? stₘ k i)
    cond₂-dec = i F.≟ dest m

-- -- data DelivResult : Set where
-- --   deliv-success : State
-- --   deliv-fail    : State

-- updates all the clocks and local state upon delivering a message
deliver-helper : State → Packet → State
deliver-helper (st i ls sentᵢ delivᵢ) (m , stₘ) =
  let j = sender m
      ls′ = stateStep ls (payload m)
      delivᵢ′ = delivTick delivᵢ j
      sentᵢ′ = sendTick sentᵢ j i
  in st i ls′ (sentᵢ′ ∨ stₘ) delivᵢ′

-- Left indicates an unsuccessful deliver, Right indicates a successful deliver
deliver : State → Packet → State ⊎ State
deliver s pckt with deliverable? s pckt
... | yes p = inj₂ (deliver-helper s pckt)
... | no ¬p = inj₁ s

stamp : State → Pid × RawMsg → Packet
stamp s (j , m) = msg (pid s) j m , clock s

-- Step the process to prepare a send
sendStep : State → Pid × RawMsg → State × Packet
sendStep s (j , m) =
  let i = pid s
      sentᵢ = sendTick (clock s) i j
      pckt = msg i j m , sentᵢ
  in record s { clock = sentᵢ } , pckt

-- TODO : Would be nice to use a state monad for this. Alas...
sendIter : State → List (Pid × RawMsg) → State × List Packet
sendIter s msgs = go s msgs []
  where
    go : State → List (Pid × RawMsg) → List Packet → State × List Packet
    go s [] pckts          = s , pckts
    go s (mⱼ ∷ msgs) pckts with sendStep s mⱼ
    ... | (s′ , pckt) = go s′ msgs (pckts ++ [ pckt ])
    

