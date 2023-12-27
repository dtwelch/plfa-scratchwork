open import Data.Bool using (Bool; true; false; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_)
open import Data.String using (String; _≟_)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

Id : Set 
Id = String 

infix  5 ƛ_⇒_
infixl 7 _·_ 
infix  8 `suc_
infix  9 `_ 

data Exp : Set where
    `_          : Id -> Exp             -- variable occurrence
    ƛ_⇒_        : Id -> Exp -> Exp      -- lamda abstraction
    _·_         : Exp -> Exp -> Exp     -- application
    `zero       : Exp                   -- zero literal
    `suc_       : Exp -> Exp            -- successor

-- some example terms/exprs...
two : Exp 
two = `suc `suc `zero

-- a value is a term/expr that corresponds to an answer
-- So the predicate Value M holds if term M is a value:
data Value : Exp -> Set where

    V-ƛ : {x : Id} {N : Exp} -> Value(`zero)

    V-zero : Value(`zero)

    V-suc : ∀ {E : Exp}
        -> Value E 
        ----------
        -> Value (`suc E)


-- substitution over closed terms/exprs 
-- (closed meaning the terms being substituted don't contain any free vars)

infix 9 _[_:=_] 

-- todo: need to learn some notation to understand this defn...
-- backtracking to p1isomorphism
