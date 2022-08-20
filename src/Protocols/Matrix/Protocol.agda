module Matrix.Protocol where


open import Data.Bool
open import Data.Fin as F hiding (_+_; _≥_)
open import Data.List hiding (lookup; merge; replicate)
open import Data.Maybe
open import Data.Nat as ℕ
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Data.Vec hiding ([_]; _++_; init)
open import Data.Vec.Properties
open import Data.Vec.Relation.Binary.Pointwise.Extensional renaming (refl to pw-refl; sym to pw-sym; trans to pw-trans)
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟨_⟩)
open import Relation.Nullary
open import Relation.Unary
open ≡-Reasoning


SqMatrix : Set → ℕ → Set
SqMatrix A n = Vec (Vec A n) n

max : ℕ → ℕ → ℕ
max n m with n ≥? m
... | yes _ = n
... | no  _ = m


module Implementation (Raw : Set) (num-site : ℕ) where

  record Message : Set where
    constructor msg
    field
      dest    : Fin num-site
      sender  : Fin num-site
      payload : Raw
      
  open Message public

  Deliv : Set
  Deliv = Vec ℕ num-site

  Sent : Set
  Sent = Vec (Vec ℕ num-site) num-site

  merge-vec : ∀{n} → Vec ℕ n → Vec ℕ n → Vec ℕ n
  merge-vec {n} x y = fx ⊛ y
    where
      fx : Vec (ℕ → ℕ) n
      fx = Data.Vec.map max x

  merge : Sent → Sent → Sent
  merge sent₁ sent₂ = fsent₁ ⊛ sent₂
    where
      fsent₁ = Data.Vec.map merge-vec sent₁

  -- TODO : Prove the merge operations correct
  
  -- For indexing into a matrix
  _[_﹐_] : Sent → Fin num-site → Fin num-site → ℕ
  s [ i ﹐ j ] = let row-vec = lookup s i in lookup row-vec j

  -- retrieve a column of a matrix
  col : ∀{A : Set} {n m} → Vec (Vec A n) m → Fin n → Vec A m
  col x j = lookup (transpose x) j

  -- for assigning to a row-col in a matrix
  _[_﹐_]≔_ : Sent → Fin num-site → Fin num-site → ℕ → Sent
  s [ i ﹐ j ]≔ k =
    let row = lookup s i
        row' = row [ j ]≔ k
    in s [ i ]≔ row'

  -- TODO: prove above operations correct

  Packet : Set
  Packet = Message × Sent

  stamp : Sent → Raw → Fin num-site → Fin num-site → Packet
  stamp s r i j = msg i j r , s 

  Delayed : Set
  Delayed = List Packet

  -- The state type for the default matrix protocol
  State₁ : Set
  State₁ = Fin num-site × Deliv × Sent × Delayed

  pid : State₁ → Fin num-site
  pid (i , _ , _ , _) = i

  -- The state type for the (potentially) optimized matrix protocol
  State₂ : Set
  State₂ = Fin num-site × Sent × Delayed

  data Action : Set where
    send_to_  : Raw → Fin num-site → Action
    deliver     : Packet → Action

  -- Updates the sent matrix for message emissions
  tick : Sent → Fin num-site → Fin num-site → Sent
  tick sent i j = let k = sent [ i ﹐ j ] in sent [ i ﹐ j ]≔ (k + 1)

  -- updates the deliver vector upon delivery
  tickD : Deliv → Fin num-site → Deliv
  tickD deliv j = let k = lookup deliv j in deliv [ j ]≔ (k + 1)
  
  -- This defines whether a vector "dominates" another vector
  _≿_ = Pointwise _≥_

  -- The predicate is decidable
  _≿?_ : ∀{n} → (x y : Vec ℕ n) → Dec (x ≿ y)
  _≿?_ {n} x y = decidable _≥?_ x y

  -- The deliverable predicate
  _deliverable-at_ : Packet → State₁ → Set
  (_ , STₘ) deliverable-at (i , d , _ , _) = d ≿ col STₘ i

  -- The deliverable predicate is decidable
  deliv? : (state : State₁) → (pckt : Packet) → Dec (pckt deliverable-at state)
  deliv? (i , deliv , _ , _) (m , STₘ) with deliv ≿? (col STₘ i)
  ... | yes p = true  because ofʸ (ext (Pointwise.app p))
  ... | no ¬p = false because ofⁿ (λ z → ¬p (ext (Pointwise.app z)))


  data DelivResult : Set where
    delivered  : Deliv → Sent → DelivResult
    ¬delivered : Deliv → Sent → DelivResult

  -- updates the state if the packet is deliverable
  δ-tick : State₁ → Packet → DelivResult
  δ-tick s@(i , deliv , sent , dq) pckt with deliv? s pckt
  ... | yes p = delivered (tickD deliv j) sent′
    where
      j = sender (proj₁ pckt)
      sent′ = merge (tick sent j i) (proj₂ pckt)
  ... | no ¬p = ¬delivered deliv sent

  -- Run through the delay queue and deliver all messages
  process-dq : State₁ → State₁
  process-dq (i , sent , deliv , dq) = go i sent deliv dq
    where
        go : Fin num-site → Deliv → Sent → Delayed → State₁
        go i deliv sent [] = i , deliv , sent , []
        go i deliv sent (pckt ∷ dq) with δ-tick (i , deliv , sent , dq) pckt
        ... | delivered deliv' sent' = go i deliv' sent' dq
        ... | ¬delivered _     _     = go i deliv  sent  dq

  -- TODO : Prove that process-dq actually delivers all readily available messages

  -- The transition coalgebra
  -- Currently using "list" for "maybe" since it makes iteration easier
  δ₁ : State₁ → Action → (List Packet × State₁)
  δ₁ (i , deliv , sent , dq) (send m to j) =
    let sent' = tick sent i j
        pckt = msg i j m , sent
    in [ pckt ] , (i , deliv , sent' , dq)
  δ₁ s@(i , deliv , sent , dq) (deliver pckt) with deliv? s pckt
  -- If deliverable, deliver it, then check if other things are now deliverable
  ... | yes _ =
    let j = sender (proj₁ pckt)
        s' = (i , tickD deliv j , tick sent j i , dq)
    in [] , process-dq s'
  -- Else, simply update the delay queue
  ... | no _ = [] , (i , deliv , sent , dq ++ [ pckt ])

  --Now define the "iterated" transition coaglebra
  δ₁⋆ : State₁ → List Action → (List Packet × State₁)
  δ₁⋆ s [] = [] , s
  δ₁⋆ s (a ∷ as) =
    let (pckts₁ , s′) = δ₁ s a
        (pckts₂ , s″) = δ₁⋆ s′ as
    in (pckts₁ ++ pckts₂ , s″)

  -- predicates indicating if an action relates to its own site
  data Loopy (i : Fin num-site) : Action → Set where
    loopy-send : ∀ m → Loopy i (send m to i)
    loopy-deliv : ∀ m STₘ → dest m ≡ i → Loopy i (deliver (m , STₘ))
  
  data Loopless (s : State₁) : List Action → Set where
    wf-emp : Loopless s []
    wf-ind : ∀ a as → ¬ Loopy (pid s) a → Loopless s as → Loopless s (a ∷ as)

  delivᵢ : State₁ → Deliv
  delivᵢ (_ , deliv , _ , _) = deliv

  sentᵢ : State₁ → Sent
  sentᵢ (_ , _ , sent , _) = sent

  zero-vec : ∀(n : ℕ) → Vec ℕ n
  zero-vec zero    = []
  zero-vec (suc n) = zero ∷ zero-vec n

  lookup-zero : ∀{n} i → lookup (zero-vec n) i ≡ zero
  lookup-zero {suc n} zero = refl
  lookup-zero {suc n} (suc i) = lookup-zero i

  zero-mat : ∀(n : ℕ) → SqMatrix ℕ n
  zero-mat n = replicate (zero-vec n)

  lookup-zero-vec : ∀{n} i → lookup (zero-mat n) i ≡ zero-vec n
  lookup-zero-vec {n} i = lookup-replicate i (zero-vec n)

  postulate
    transpose-zero : ∀{n} → zero-mat n ≡ transpose (zero-mat n)
    -- transpose-zero {zero} = refl
    -- transpose-zero {suc n} = {!!}


  IsZeroVec : ∀{n} → Vec ℕ n → Set
  IsZeroVec {n} x = Pointwise _≡_ x (zero-vec n)

  IsZeroMat : ∀{n} → SqMatrix ℕ n → Set
  IsZeroMat {n} x = ∀ i → IsZeroVec (lookup x i)

  dumb : ∀{n} → IsZeroMat (zero-mat n)
  dumb {zero} = λ i → ext (λ ())
  dumb {suc n} = λ i → ext (λ j  → {!!})

  data Init : State₁ → Set where
    init : ∀ i deliv sent → IsZeroVec deliv → IsZeroMat sent →
           Init (i , deliv , sent , [])

  deliv-invariant : ∀ s s′ actions pckts → Init s → Loopless s actions → δ₁⋆ s actions ≡ (pckts , s′) →
                    Pointwise _≡_ (delivᵢ s′) (col (sentᵢ s′) (pid s′))
  deliv-invariant .(i , deliv , sent , []) .(i , deliv , sent , []) [] .[] (init i deliv sent deliv≡0 sent≡0) loopless refl = ext prf
    where
      prf : ∀(k : Fin num-site) → lookup (delivᵢ (i , deliv , sent , [])) k ≡ lookup (col (sentᵢ (i , deliv , sent , [])) (pid (i , deliv , sent , []))) k
      prf k =
        lookup (delivᵢ (i , deliv , sent , [])) k                 ≡⟨ refl ⟩
        lookup deliv k                                            ≡⟨ cong (λ z → lookup z k) (Pointwise-≡⇒≡ deliv≡0) ⟩
        lookup (zero-vec num-site) k                              ≡⟨ cong (λ z → lookup z k) (sym (lookup-zero-vec i)) ⟩
        lookup (lookup (zero-mat num-site) i) k                   ≡⟨ cong (λ z → lookup (lookup z i) k) transpose-zero ⟩
        lookup (lookup (transpose (zero-mat num-site)) i) k       ≡⟨ refl ⟩
        lookup (col (zero-mat num-site) i) k                      ≡⟨ refl ⟩
        lookup (col (replicate (zero-vec num-site)) i) k          ≡⟨ cong (λ z → lookup (col z i) k) (Pointwise-≡⇒≡ (pw-sym {!!} {!!})) ⟩
        lookup (col sent i) k                                     ≡⟨ refl ⟩
        lookup (col (sentᵢ (i , deliv , sent , [])) (pid (i , deliv , sent , []))) k  ∎
  deliv-invariant s s′ (x ∷ actions) pckts init-s loopless s⟶⋆s′ = {!!}
                    


