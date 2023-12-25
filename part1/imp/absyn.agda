module absyn where 

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning

open import Data.Bool using (Bool; true; false; if_then_else_; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_)
open import Data.String using (String; _==_; _≟_)
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Agda.Builtin.Char

open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)

-- variable and procedure names are strings
vname : Set -- variable names
vname = String

pname : Set -- procedure names 
pname = String 

is-global : vname -> Bool 
is-global name with (primStringToList name)
...    | []       = true 
...    | (x ∷ xs) = primCharEquality x 'G' 

is-local : vname -> Bool 
is-local name = not (is-global name)

-- values and primitive values are usually part of the semantics, however, as they
-- occur as literals in the abstract syntax, we already define them here.

pval : Set 
pval = ℕ 

val : Set 
val = ℕ -> pval