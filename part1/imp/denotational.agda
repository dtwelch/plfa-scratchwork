module denotational where 


open import Data.Bool using (Bool; true; false; if_then_else_; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_)
open import Data.String using (String; _==_; _≟_)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

-- variable Identifiers
Id : Set 
Id = String

-- states 
State : Set
State = Id -> ℕ

-- note; look at the definition above ^^ and in the way the st_update
-- fn works below 
--  any term of the form λ (x : Id) -> 0 (any lambda with type Id -> ℕ really) 
-- is shorthand for a State (it's a type synonym)

-- state update fn


_[_->>_] : Id -> ℕ -> State -> State
_[_->>_] name val s = 
    λ (name' : Id) -> if name == name' then val else (s name')

infixr 9 _[_->>_] 


-- in our sample language, we deliberately leave the 
-- syntax of arithmetic and boolean expressions unspecified.
-- You technically have two choices:
-- 1. model both boolean and arithmetic expressions with explicitly 
--    defined type hierarchies (deep embeddeding)
-- 2. decide that an "arithmetic expression" is just a function from
--    states to numbers (e.g., State -> ℕ) and a boolean expression 
--    is a predicate over states, State -> 𝔹. A State is a mapping from
--    program variables to values. E.g., a /= b would be represented
--    by the predicate fun s : State => s("a") /= s("b"). This is 
--    a *shallow embedding* since we're just using functions as shorthand
--    to avoid defining abstract syntax trees (so we don't need to define
--    a sematics for these trees -- e.g., an 'eval(..)' fn) 

-- data Stmt : Set where 
--    assign : Id -> ( 