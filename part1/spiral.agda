module spiral where
open import Data.Nat  using (ℕ; zero; suc; _*_; _+_; _∸_; _≡ᵇ_)
-- open import Agda.Utils.Function

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)

open import Agda.Builtin.Nat
open import Data.Empty
open import Data.Unit.Base

-- Positive n is a constraint which is unsatisfiable for the
-- first two natural numbers
-- see: https://stackoverflow.com/questions/40098289/how-do-i-implement-positive-numbers-in-agda
Positive : ℕ -> Set
Positive zero       = ⊥
Positive (suc zero) = ⊥
Positive _          = ⊤

data ℕ² : Set where
    two  : ℕ²
    succ : ℕ² -> ℕ²

toℕ² : ∀ n {_ : Positive n} -> ℕ²
toℕ²  0 {()}
toℕ²  1 {()}
toℕ² (suc (suc zero))       = two
toℕ² (suc (suc (suc n)))    = succ (toℕ² (suc (suc n))) 

{-# BUILTIN FROMNAT toℕ² #-}


{-  
-- works..
fail : ℕ²
fail = 0

fail2 : ℕ²
fail2 = 1

ok : ℕ²
ok = 2

ok' : ℕ²
ok' = 3
-}

-- Sp_Loc - 'Spiral Location'
-- cen(k) - the central spiral location
-- ss(k)(p) -- the spiral successor (ss) of location p for a spiral of arity k
-- rs(k)(p) -- the radial successor (rs) .. "      
data Sp_Loc (A : Set) : ℕ² -> Set where
    Cen : (k : ℕ²) ->  Sp_Loc A k                
    SS  : (k : ℕ²) -> (Sp_Loc A k) -> Sp_Loc A k 
    RS  : (k : ℕ²) -> (Sp_Loc A k) -> Sp_Loc A k 

{-
-- pty1
inf : {A : Set} 
    (∀ k : ℕ²) 
    (∀ p : Sp_Loc A k) -> 
    (∃ n : ℕ²) -> 
        iterate' n ss 
-}

-- pty3:
cen-rt : ∀ {A : Set} -> ∀ (k : ℕ²)
    -> RS k (Cen k) ≡ SS k (Cen k)
cen-rt k = {!   !} 