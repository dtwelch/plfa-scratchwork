module absyn where 

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning

open import Data.Bool using (Bool; 𝔹; true; false; if_then_else_; T; not)
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

-- arithmetic expressions consist of constants, indexed array vars, and unary and binary
-- operator applications. The underlying operator type (binary or unary function) is stored 
-- in the corresponding abstract syntax node -- so a BinOpExp(op, l, r) should be thought of 
-- as the application of some binary operator o to expression (arguments) l and r (i.e.: l op r)

data AExp : Set where 
    num_exp   : ℕ -> AExp
    varid_exp : vname -> AExp
    unop_exp  : (ℕ -> ℕ) -> AExp -> AExp 
    binop_exp : (ℕ -> ℕ -> ℕ) -> AExp -> AExp -> AExp

-- boolean expressions consist of constants, not operator applications,
-- as well as binary connective and comparison operator applications 
-- (the underlying functions, as with arithmetic expressions, for such 
-- application expressions are stored in the node's themselves as higher
-- order unary or binary functions)

-- so in the type definition below, the binop_exp constructor takes a 
-- binary function intended to be any of: and, or, xor, etc followed by
-- a left and right argument (boolean) exp.

data BExp : Set where 
    bconst_exp : Bool -> BExp
    bnot_exp   : BExp -> BExp  -- nb: explicitly modeled (no higher order fn needed for this node)
    binop_exp  : (Bool -> Bool -> Bool) -> BExp -> BExp -> BExp
    cmpop_exp  : (ℕ -> ℕ -> Bool) -> AExp -> AExp -> BExp

-- commands can roughly be put into five categories:
--
-- skip                - the no-op command
--
-- assignment commands - commands to assign the value of an AExp, copy or clear arrays
--                       and a command to simultaneously assign all local variables, 
--                       which will only be used internally to simplify the definition a 
--                       small step sematics
-- 
-- block commands      - standard sequential composition commands, if-then-else, and while 
--                       commands + a scope command which executes a command with a fresh 
--                       set of local variables
-- 
-- procedure commands  - procedure call, and a procedure scope command which executes a 
--                       command in a specified procedure environment. Similar to the 
--                       scope command, which introduces new local variables limiting the 
--                       effects of variable manipulations to the content of the command.
--                       The procedure scope command introduces new procedures, and limits
--                       the validity of their names to the content of the command. 

data Command : Set where
    skip_cmd            : Command 
    assignidx_cmd       : vname -> AExp -> AExp -> Command  -- arr[i] := x;
    arraycopy_cmd       : vname -> vname -> Command         -- arr[] = someOtherArray;
    arrayclear_cmd      : vname -> Command                  -- clear(arr[]);
    assign_locals_cmd   : (vname -> val) -> Command         -- assign to all local vars