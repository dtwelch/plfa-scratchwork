module sp_loc where 

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-comm; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+)
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

to-nat : ℕ² -> ℕ
to-nat two = 2
to-nat (succ k) = 1 + to-nat k

--data Sp_Loc : Nat -> Set where

data SpLoc (A : Set) : ℕ² -> Set where
    cen : (k : ℕ²) -> (SpLoc A k)               -- center loc
    ss  : (k : ℕ²) -> (SpLoc A k) -> SpLoc A k  -- spiral successor
    rs  : (k : ℕ²) -> (SpLoc A k) -> SpLoc A k  -- radial successor

iterated : ∀ {A : Set}  -> (f : A -> A) -> ℕ -> A -> A
iterated f zero x = x
iterated f (suc n) x = f (iterated f n x)
-- postulates
{-
postulate        
    -- left side of hypo: iterate' the (SS k) function m times starting from (Cen k)
    pty2 : ∀ (k : ℕ²) -> ∀ (m n : ℕ) 
        -> iterate' m (SS k) (Cen k) ≡ iterate' n (SS k) (Cen k) 
        ---------------------------------------------------------
        -> m ≡ n 
-}

inv-lemma : ∀ m -> m + 1 ≡ suc m
inv-lemma m =
    begin 
        m + 1
    ≡⟨ (+-comm m 1) ⟩ 
        suc m
    ∎ 
-- spiral center dist.
scd : ∀ {A : Set} -> ∀ {k : ℕ²} -> (SpLoc A k) -> ℕ
scd {A} {k} (cen k)   = 0
scd {A} {k} (ss k p)  = (scd p) + 1
scd {A} {k} (rs k p)  = (to-nat k) * (scd p) + 1  -- how many sploc's skipped in general?

scd-03 : ∀ {A : Set} -> ∀ (k : ℕ²) -> ∀ (n : ℕ) -> scd ( iterated (ss k) n (cen k) ) ≡ n 
scd-03 {A} k 0 =
    begin
        scd (iterated (ss k) zero (cen k))
    ≡⟨⟩ -- by base case of iterated fn (it's a defining equation)
        scd (cen k)
    ≡⟨⟩
        0 
    ∎ 
scd-03 {A} k (suc n) = 
    begin
        scd (iterated (ss k) (suc n) (cen k))
    ≡⟨⟩ -- by ind. case of iterated fn
        scd ( (ss k) (iterated (ss k) n (cen k)) )
    ≡⟨⟩ 
        (scd (iterated (ss k) n (cen k))) + 1
    ≡⟨ +-comm (scd (iterated (ss k) n (cen k))) 1 ⟩ 
        1 + scd (iterated (ss k) n (cen k)) 
    ≡⟨⟩ 
        suc ( scd (iterated (ss k) n (cen k)) ) 
    ≡⟨ cong (suc) (scd-03 {A} k n)  ⟩
        suc n 
    ∎ 
{- scd-03 {A} k (suc n) = 
    begin
        scd (iterated (ss k) (suc n) (cen k))
    ≡⟨⟩ -- by ind. case of iterated fn
        scd ( (ss k) (iterated (ss k) n (cen k)) )
    ≡⟨⟩ 
        (scd (iterated (ss k) n (cen k))) + 1
    ≡⟨ +-comm (scd (iterated (ss k) n (cen k))) 1 ⟩ 
        suc (scd (iterated (ss k) n (cen k)))  
    ≡⟨ cong (suc) (scd-03 {A} k n) ⟩ -- cong (suc) (scd-03 {A} k n) ⟩ 
        suc n  
    ∎
-}
-- cong (suc) (scd-03 {A} k n)
--scd (iterated (ss k) n (cen k)) + 1

-- ?1 : scd (ss k (iterated (ss k) n (cen k))) ≡ suc n


