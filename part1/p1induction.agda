module p1induction where

import Data.Nat
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat  using ( zero; suc; _*_; _∸_; _≡ᵇ_) renaming (ℕ to N'; _+_ to _+'_)
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not; if_then_else_)

--_+'_ : N' ->  N' ->  N'
--zero +' n = n
--(suc m) +' n = suc (m +' n)
--infixl 30 _+'_

+-assoc : ∀ (m n p : N') -> (m +' n) +' p ≡ m +' (n +' p)
-- first need to estbalish the base case of the property trying to be proved..
+-assoc zero n p =
  begin
    (zero +' n) +' p
  ≡⟨⟩
    n +' p
  ≡⟨⟩
    zero +' (n +' p)
    -- (ii) by def of _+'_ .. steps:
    -- matches pattern for second case of _+'_, so can be rewritten to zero' + (n + p)
  ∎
-- trying now to show:
-- (suc m + n) + p ≡ suc m + (n + p)
+-assoc (suc m) n p =
  begin
    ((suc m +' n) +' p)
  ≡⟨⟩      -- v -
    (suc (m +' n)) +' p
  ≡⟨⟩
    suc ((m +' n) +' p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m +' (n +' p))
  ≡⟨⟩
    suc m +' (n +' p)
  ∎

-- Lemma +-id-right (+ has a right identity of zero)
+-id-right : ∀ (m : N') -> m +' zero ≡ m
+-id-right zero =
  begin
    zero +' zero
  ≡⟨⟩
    zero
  ∎ -- (suc m) +' zero ≡ m
+-id-right (suc m) =
  begin
    (suc m) +' zero
  ≡⟨⟩
    suc (m +' zero)
  ≡⟨⟩
    suc (m +' zero)
  ≡⟨ cong suc (+-id-right m) ⟩
    suc m
  ∎

-- Lemma +-suc (moves the successor app 'outwards')
+-suc : ∀ (m n : N') -> m +' suc n ≡ suc (m +' n)
+-suc zero n =
  begin
    zero +' (suc n)
  ≡⟨⟩
    (suc n)
  ∎
+-suc (suc m) n =
  begin
    suc m +' suc n
  ≡⟨⟩
    suc (m +' suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m +' n))
  ∎

+-comm : ∀ (m n : N') -> m +' n ≡ n +' m
+-comm m zero =
  begin
    m +' zero
  ≡⟨ +-id-right m ⟩
    m
  ≡⟨⟩
    zero +' m
  ∎
+-comm m (suc n) = -- must show for inductive case: m + suc n ≡ suc n + m
  begin
    m +' suc n
  ≡⟨ +-suc m n ⟩
    suc (m +' n)
    -- if f is a fn and e is proposition (say x ≡ y),
    -- then the application (cong f e) gives back: f(x) ≡ f(y)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n +' m)
  ≡⟨⟩
    suc n +' m
  ∎

-- Corollary +-rearrange:
-- needs : +-assoc : ∀ (m n p : N') -> (m +' n) +' p ≡ m +' (n +' p)
+-rearrange : ∀ (m n p q : N') -> (m +' n) +' (p +' q) ≡ m +' (n +' p) +' q
+-rearrange m n p q =
  begin
    (m +' n) +' (p +' q)
  ≡⟨ +-assoc m n (p +' q) ⟩
    m +' (n +' (p +' q))
  ≡⟨ cong (m +'_) (sym (+-assoc n p q)) ⟩
    m +' ((n +' p) +' q)
  ≡⟨ sym (+-assoc m (n +' p) q) ⟩
    (m +' (n +' p)) +' q
  ∎

-- +-assoc-alt : ∀ (m n p : ℕ) → (m +' n) +' p ≡ m +' (n +' p)
-- +-assoc-alt zero    n p   =      refl
-- +-assoc-alt (suc m) n p   =   rewrite +-assoc-alt m n p  refl
-- i.e., ind. case needs to show:
--  (suc m +' n) +' p ≡ suc m +' (n +' p)
--  simplyfing by using the ind. case from the def of +' gives:
--  suc ((m +' n) +' p) ≡ suc (m +' ( n +' p))
--  after rewriting with the inductive hypothesis, these two terms are equal,
--  and the proof is given by refl.
 
data Bin : Set where 
  ⟨⟩ : Bin 
  _O : Bin → Bin 
  _I : Bin → Bin 

-- inc : Bin -> Bin 
-- inc (⟨⟩ O O O O) = ⟨⟩ O O O I
