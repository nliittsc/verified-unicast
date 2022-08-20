module Abstractions.MonadPractice where


open import Data.String using (String; _++_)
open import Data.Unit
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
{-
  Interactions with Network Env:
    1. Send
    2. Recv
-}

-- "uninterpretted actions"
data Action : Set where
  send : String → Action
  recv : Action

data Trace (A : Set) : Set where
  await : A → Trace A
  step  : Action → Trace A → Trace A

ex₁ : Trace String
ex₁ = await "hello"

ex₂ : Trace String
ex₂ = step recv ex₁

ex₃ : String → Trace String
ex₃ str = await (str ++ " world")



{-
  Monad Functions:
    return : a → m a
    join   : m (m a) → m a
    fmap   : (a → b) → (m a → m b)

  Monad Laws:
    fmap-id : fmap id = id
    fmap-∘  : fmap (f ∘ g) = fmap f ∘ fmap g
    (left-identity below)
    join-of-fmap-return : (join ∘ fmap return) = id
    (todo : right-identity)
-}

-- This is a functor
-- TODO: prove functor laws?
fmap : ∀{A B} → (A → B) → (Trace A → Trace B)
fmap f (await a)     = await (f a)
fmap f (step act ta) = step act (fmap f ta)

return : ∀{A} (a : A) → Trace A
return a = await a

join : ∀{A} → Trace (Trace A) → Trace A
join (await tta) = tta
join (step x tta) = step x (join tta)

_>>=_ : ∀{A B} → Trace A → (A → Trace B) → Trace B
x >>= f = join (fmap f x)

_>>_ : ∀{A B} → Trace A → Trace B → Trace B
x >> y = x >>= λ _ → y

ex₄ : ex₂ >>= ex₃ ≡ step recv (await "hello world")
ex₄ =
  ex₂ >>= ex₃                                                      ≡⟨⟩
  join (fmap ex₃ ex₂)                                              ≡⟨⟩
  join (fmap ex₃ (step recv ex₁))                                  ≡⟨⟩
  join (step recv (fmap ex₃ ex₁))                                  ≡⟨⟩
  step recv (join (fmap ex₃ ex₁))                                  ≡⟨⟩
  step recv (join (fmap ex₃ (await "hello")))                      ≡⟨⟩
  step recv (join (await (ex₃ "hello")))                           ≡⟨⟩
  step recv (join (await ((λ x → await (x ++ " world")) "hello"))) ≡⟨⟩
  step recv (join (await (await "hello world")))                   ≡⟨⟩
  step recv (await "hello world")                                  ∎
  where open Eq.≡-Reasoning
  
{-
main s = do
  m <- receive
  let s' = update m s
      msgs = getSends s'
  sendAll msgs
-}

receive : Trace String
receive = await {!!}

‵send : String → Trace ⊤
‵send str = step (send str) (await tt)


module _ where

  data State : Set where

  update : String → State → State
  update _ ()

  getWork : State → String
  getWork ()

{-# NON_TERMINATING #-}
echo : Trace ⊤
echo = do
  m <- receive
  ‵send m
  echo



main : State → Trace ⊤
main s = do
  m <- receive
  let s' = update m s
      m' = getWork s'
  ‵send m'



-- P ⟶ P'     Q ⟶ Q'
-- ---------------------
--  P || Q ⟶ P' || Q'

-- step s a ≡ s' ⇔ s =[ a ]⇒ s'


-- Π[ i ] = s
-- s =[ a ]⇒ s'
-- -------------
-- Π -[ a ]→ Π[ i ]≔ s'





