module sp_loc where 

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.part1.Isomorphism using (_≃_; _⇔_)

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

--data Sp_Loc : Nat -> Set where

data SpLoc (A : Set) : ℕ² -> Set where
    Cen : (k : ℕ²) ->  SpLoc A k                
    SS  : (k : ℕ²) -> (SpLoc A k) -> SpLoc A k 
    RS  : (k : ℕ²) -> (SpLoc A k) -> SpLoc A k 

-- postulates
postulate        
    -- left side of hypo: iterate' the (SS k) function m times starting from (Cen k)
    pty2 : ∀ (k : ℕ²) -> ∀ (m n : ℕ) 
        -> iterate' m (SS k) (Cen k) ≡ iterate' n (SS k) (Cen k) 
        ---------------------------------------------------------
        -> m ≡ n 