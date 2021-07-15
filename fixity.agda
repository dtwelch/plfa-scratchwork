module fixity where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _∸_; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not; if_then_else_)

_and'_ : Bool -> Bool -> Bool
_and'_ = _∧_

_+'_ : ℕ -> ℕ -> ℕ
_+'_ = _+_

_,_[_,[_]] : ℕ -> ℕ -> ℕ -> ℕ -> ℕ
_,_[_,[_]] = {!   !}
-- •,•[•,[•]]
infixl 30 _,_[_,[_]]

mixfix-tst : ∀ (a b c d : ℕ) -> a , b [ c ,[ d ]] ≡ d
mixfix-tst = {!   !}

-- took long to figure out.. (how to import _==_ from data.nat)
-- needed to look at:
-- https://agda.github.io/agda-stdlib/Data.Nat.Base.html
_=='_ : ℕ -> ℕ -> Bool
_=='_ = _≡ᵇ_

infix  40 _!
infixl 30 _+'_
infix  25 _=='_
infixr 20 _and'_
  
_! : ℕ -> ℕ
zero ! = 1
(suc n) ! = (suc n) * ( n ! )
--tst0 : {x y z : ℕ} -> x + y + z ≡ ((x + y) + z)    -- works
--tst0 : {x y z : ℕ} -> x + y + z ≡ (x + y) + z        -- works
--tst0 : {x y z : ℕ} -> x + y + z ≡ x + (y + z)      -- won't work (since + is actually infixl)
tst0 : {x y z : ℕ} -> x +' y +' z ≡ (x +' y) +' z --works
tst0 = refl

if'_then_else_ : ∀ {ℓ} {A : Set ℓ} -> Bool -> A -> A -> A
if'_then_else_ = if_then_else_

tst : {a b c : Bool} -> a ∧ b ∧ c ≡ a ∧ (b ∧ c)    -- works
--tst : {a b c : Bool} -> a ∧ b ∧ c ≡ (a ∧ b) ∧ c  -- won't work (since ∧ is infixr)
tst = refl

tst2 : {b : Bool} {n : ℕ} ->
  b and' n +' n ==' n   ≡ b and' (n +' n ==' n)
tst2 = refl

tst3 : {b : Bool} {n : ℕ} ->
  b and' n +' n ==' n   ≡ (b) and' ((n +' n) ==' n)
tst3 = refl

tst4 : {b : Bool} {n : ℕ} ->
  b and' n +' n ==' n   ≡ (b) and' ((n +' n) ==' n)
tst4 = refl

tst5 : {b : Bool} {n : ℕ} ->
  b and' n +' n ==' n !   ≡ (b) and' ((n +' n) ==' ((n) !))
tst5 = refl

{--
+-assoc : ∀ (m n p : Nat') -> (m +' n) +' p ≡ m +' (n +' p)
-- first need to estbalish the base case of the property trying to be proved..
+-assoc zero' n p =
  begin
    (zero' +' n) +' p
  ≡⟨⟩
    n +' p
  ≡⟨⟩
    zero' +' (n +' p)
    -- (ii) by def of _+'_ .. steps:
    -- matches pattern for second case of _+'_, so can be rewritten to zero' + (n + p)
  ∎
-- trying now to show:
-- (suc m + n) + p ≡ suc m + (n + p)
 +-assoc (suc' m) n p =
  begin
    (suc' m +' n) +' p
  ≡⟨⟩
    suc' (m +' n) +' p
  ≡⟨⟩
    (suc' m) +'
--}
