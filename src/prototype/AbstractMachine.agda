module AbstractMachine where

open import Data.List
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.String using (String)
open ≡-Reasoning

--- Programming Language ---

data Expr : Set
data Cmd : Set


Loc = ℕ

data Expr where
  ♯ : String → Expr
  ƛ_·_ : String → Expr → Expr
  _⦅_⦆ : Expr → Expr → Expr
  cmd⟨_⟩ : Cmd → Expr


data Cmd where
  bnd_⟵_︔_ : String → Expr → Cmd → Cmd
  ret[_] : Expr → Cmd
  send⟨_,_⟩ : Expr → Loc → Cmd
  recv : Cmd


--- Simplified Language ---

record Msg : Set where
  constructor M
  field
    sender : Loc
    dest : Loc
    contents : String


data Op : Set where
  send⟨_⟩ : Msg → Op
  recv : Op

Program = List Op


--- Atomic Actions ---

data Act : Set where
  send : Msg → Act
  post : Msg → Act
  get : Act
  recv : Act

--- Local State ---

data OState : Set where
  idle : List Msg → OState
  Post⟨_⟩ : Msg → List Msg → OState

data IState : Set where
  idle : List Msg → IState
  Dlvr⟨_⟩ : Msg → List Msg → IState


data Config : Set where
  ⟨_,_⟩ : Program → (OState × IState) → Config


data _⟨_⟩⟼_ : Config → Act → Config → Set where
  send : ∀{m p ob ib} → ⟨ send⟨ m ⟩ ∷ p , {!(ob , is)!} ⟩ ⟨ send m ⟩⟼ {!!}



