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
open import Data.Maybe

-- variable and procedure names are strings
vname : Set
vname = String

pname : Set -- procedure names 
pname = String 

is-global : vname -> Bool 
is-global name with (primStringToList name)
...    | []       = true
...    | (x ∷ xs) = primCharEquality x 'G' 

is-local : vname -> Bool 
is-local name = not (is-global name)

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
    -- no-op
    skip                : Command 

    -- assignment
    _[_]:=_             : vname -> AExp -> AExp -> Command  
    _[]:=_              : vname -> vname -> Command         
    clear_              : vname -> Command                  
    assign_locals_cmd   : (vname -> val) -> Command         -- assign to all local vars simultaneously

    _`_                 : Command -> Command -> Command
    scope_cmd           : Command -> Command 
    -- proc
    procscope_cmd       : pname -> Maybe (Command × Command) -> Command

-- the state maps variable names to values 
State : Set 
State = vname -> val

-- some syntax for the null state and a state where only certain variables 
-- are set

-- the null state
<> : State 
<> = λ vname -> λ y -> 0  -- so is our default initial value

-- state combination
-- the state combination operator constructs a state by taking the local variables
-- from one state and the globals from another state

<_!_> : State -> State -> State
<_!_> s t = λ (n : vname) -> if (is-local n) then (s n) else (t n)

-- now we prove some basic facts.

combine-collapse : ∀ (s : State) -> < s ! s > ≡ s 
combine-collapse s = 
    begin
        < s ! s >
    ≡⟨⟩
       -- λ (n : vname) -> (if is-local n then s else s) n   
        < (λ n -> s n) ! (λ n -> s n) > 
    ≡⟨ {!   !} ⟩ 
        {!   !}
    ∎ 

piecewise : ∀ {A : Set} -> (ℕ -> A) -> (ℕ -> A) -> (ℕ -> A) -> ℕ -> A
piecewise f g h = λ x -> if true then f x 
                        else if true then g x 
                        else h x 