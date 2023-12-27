module p1induction where

import Data.Nat
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat  using (ℕ; zero; suc; _*_; _+_; _∸_; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not; if_then_else_)

-- _+'_ : N' ->  N' ->  N'
-- zero +' n = n
-- (suc m) +' n = suc (m +' n)
-- infixl 30 _+'_

+-assoc : ∀ (m n p : ℕ) -> (m + n) + p ≡ m + (n + p)
-- first need to estbalish the base case of the property trying to be proved..
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
    -- (ii) by def of _+'_ .. steps:
    -- matches pattern for second case of _+'_, so can be rewritten to zero' + (n + p)
  ∎
-- trying now to show:
-- (suc m + n) + p ≡ suc m + (n + p)
+-assoc (suc m) n p =
  begin
    ((suc m + n) + p)
  ≡⟨⟩      -- v -
    (suc (m + n)) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

-- Lemma +-id-right (+ has a right identity of zero)
+-id-right : ∀ (m : ℕ) -> m + zero ≡ m
+-id-right zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎ -- (suc m) +' zero ≡ m
+-id-right (suc m) =
  begin
    (suc m) + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-id-right m) ⟩
    suc m
  ∎

-- Lemma +-suc (moves the successor app 'outwards')
+-suc : ∀ (m n : ℕ) -> m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + (suc n)
  ≡⟨⟩
    (suc n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ∎

+-comm : ∀ (m n : ℕ) -> m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-id-right m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) = -- must show for inductive case: m + suc n ≡ suc n + m
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
    -- if f is a fn and e is proposition (say x ≡ y),
    -- then the application (cong f e) gives back: f(x) ≡ f(y)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

-- Corollary +-rearrange:
-- needs : +-assoc : ∀ (m n p : N') -> (m +' n) +' p ≡ m +' (n +' p)
+-rearrange : ∀ (m n p q : ℕ) -> (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
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

-- commutativity with rewrite (practice from the prior ch)
+-id' : ∀ (n : ℕ)
  ----------------
  -> n + zero ≡ n
+-id' zero = refl
+-id' (suc x) rewrite +-id' x = refl

+-suc' : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc' zero n = refl
+-suc' (suc m) n rewrite +-suc' m n = refl

_test : zero + suc 1 ≡ suc (zero + 1)
_test = refl  -- the terms are definitionally equal, see base case for _+_

+-comm' : ∀ (m n : ℕ) -> m + n ≡ n + m
+-comm' m zero    rewrite +-id' m = refl
+-comm' m (suc n) rewrite +-suc' m n | +-comm' m n = refl
-- the bar | allows us to use *two* equations:
--   +-suc' m n [m + (suc n) ≡ suc (m + n)] and
--   +-comm' m n [m + n ≡ n + m]
-- NOTE: order of rewrites specified between |s matter
-- so rewrite.. here are the sequence of rewrites here (I think):
-- initially we apply the first rewrite rule
--      +-suc' m n [m + (suc n) ≡ (suc n) + m] to get:
--          suc (m + n) ≡ (suc n) + m
--        then we simplify r.h.s using the suc constructor from _+_
--        suc (n + m) to get:
--          suc (m + n) ≡ suc (n + m)
--        now the +-comm' m n rewrite rule will come in handy to achieve:
--          suc (n + m) ≡ suc (n + m)
--        and we can solve using reflexivity (refl)

-- associativity with rewrite (practice from the prior ch)
+-assoc' : ∀ (m n p : ℕ)
  -------------------------
  -> (m + n) + p ≡ m + (n + p)
+-assoc' zero y z     = refl
+-assoc' (suc x) y z rewrite +-assoc' x y z = refl

+-assoc2 : ∀ (m n p : ℕ) -> (m + n) + p ≡ m + (n + p) 
+-assoc2 zero n p = refl
+-assoc2 (suc m) n p = (cong suc {(m + n) + p} {m + (n + p)}) (+-assoc2 m n p) 
                                -- note: ^ filling in the implicits with what we're trying to prove 
                                -- equivalents of... then applying suc to that

-- +-comm' : ∀ (m n : ℕ) -> m + n ≡ n + m

+-swap : ∀ (m n p : ℕ) -> m + (n + p) ≡ n + (m + p)
+-swap m n p 
  rewrite +-comm n (m + p)   -- goal after: m + (n + p) ≡ (m + p) + n
  rewrite +-assoc2 m p n      -- goal after: m + (n + p) ≡ m + (p + n)
  rewrite +-comm p n = refl  -- goal after: m + (p + n) ≡ m + (p + n)

-- +-comm' : ∀ (m n : ℕ) -> m + n ≡ n + m

-- +-assoc eq proof

+-assoc3 : ∀ (m n p : ℕ) -> (m + n) + p ≡ m + (n + p)
+-assoc3 zero n p =
  begin
    (zero + n) + p 
  ≡⟨⟩
    n + p 
  ≡⟨⟩
    zero + (n + p)
   ∎
+-assoc3 (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc3 m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
   ∎



-- _+'_ : N' ->  N' ->  N'
-- zero +' n = n
-- (suc m) +' n = suc (m +' n)
-- infixl 30 _+'_

*-distrib-+' : ∀ (m n p : ℕ) -> (m + n) * p ≡ m * p + n * p
*-distrib-+' zero n p =
  begin 
    (zero + n) * p  -- (zero + n) * p ≡ zero * p + n
  ≡⟨⟩
    n * p
  ≡⟨⟩
    (zero * p) + n * p
  ≡⟨⟩ 
    zero + n * p
  ≡⟨⟩
    n * p
   ∎
-- _*_ : ℕ -> ℕ -> ℕ
-- zero    * n  =  zero
-- (suc m) * n  =  n + (m * n)

-- *-distrib-+' : ∀ (m n p : ℕ) -> (m + n) * p ≡ m * p + n * p

*-distrib-+' (suc m) n p = -- (suc m + n) * p ≡ suc m * p + n * p
  begin
    (suc m + n) * p
  ≡⟨⟩
    suc (m + n) * p
  ≡⟨⟩
    p + ((m + n) * p)
  ≡⟨ cong (p +_) (*-distrib-+' m n p) ⟩  -- *-distrib-+' m n p only gives a term
                                         -- of the form: (m + n) * p
                                         -- the cong combinator applied to the (p +_)
                                         -- partial application gives evidence of a term:
                                      -- p + ((m + n) * p) (which is the one we need to match against)
    p + (m * p + n * p) 
  ≡⟨ sym (+-assoc2 p (m * p) (n * p)) ⟩ -- sym 'flips' the instantiated assoc proof
    (p + m * p) + n * p  -- sym (+-assoc2 p (m * p) (n * p)) 
    ∎
   -- +-assoc2 : ∀ (m n p : ℕ) -> (m + n) + p ≡ m + (n + p)
 
*-distrib-+ : ∀ (m n p : ℕ) -> (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p                   -- gives (suc m + n) * p ≡ suc m * p + n * p which becomes:
                                          -- (m + n * m) + p
   rewrite *-distrib-+ m n p    -- p + (m * p + n * p) ≡ p + m * p + n * p
  rewrite sym (+-assoc2 p (m * p) (n * p)) = refl

    -- ?0 : p + (m * p + n * p) ≡ p + m * p + n * p
-- idea: use +-assoc....
-- closer: 
  -- cong suc {m * p + n * p} {m * p + n * p} (*-distrib-+ m n p)

-- cong suc {m * p + n * p} {m * p + n * p} (*-distrib-+ m n p) 

-- cong suc {m * p + n * p} {m * p + n * p} has type: 
-- ∀ (m n p : ℕ) -> m * p + n * p ≡ m * p + n * p -> suc(m * p + n * p) ≡ suc(m * p + n * p)
-- (suc m + n) * p ≡ suc m * p + n * p becomes
-- (n * m) + m                        (by ind. hyp)
-- 
   -- n * p + p * m  
*-assoc : ∀ (m n p : ℕ) -> (m * n) * p ≡ m * (n * p)
*-assoc zero n p = 
  begin 
    (zero * n) * p
  ≡⟨⟩
    zero * p
  ≡⟨⟩
   zero
  ≡⟨⟩
   zero * (n * p)
  ≡⟨⟩
   zero
  ∎

-- _*_ : ℕ -> ℕ -> ℕ
-- zero    * n  =  zero
-- (suc m) * n  =  n + (m * n)

-- *-distrib-+' : ∀ (m n p : ℕ) -> (m + n) * p ≡ m * p + n * p
-- *-assoc      : ∀ (m n p : ℕ) -> (m * n) * p ≡ m * (n * p)
-- +-assoc3     : ∀ (m n p : ℕ) -> (m + n) + p ≡ m + (n + p)
*-assoc (suc m) n p = 
  begin -- (suc m) * n  =  n + (m * n)
    (suc m * n) * p
  ≡⟨⟩
    (n + (m * n)) * p 
  ≡⟨ (*-distrib-+' n (m * n) p) ⟩ 
    n * p + ((m * n) * p)
    -- goal: n * p + m * n * p ≡ n * p + m * (n * p)
  ≡⟨ cong ((n * p) +_ ) (*-assoc m n p) ⟩  
            -- constructing a term 
            -- of the right shape w/ the help of the 
            -- ind. hypothesis (app of *-assoc) 
    n * p + (m * (n * p)) 
  ∎

-- with rewrite ind. def (without chains of equations)
*-assoc' : ∀ (m n p : ℕ) -> (m * n) * p ≡ m * (n * p)
*-assoc' zero n p = refl
*-assoc' (suc m) n p 
  rewrite (*-distrib-+' n (m * n) p) 
  rewrite (cong ((n * p) +_ ) (*-assoc m n p)) = refl

-- _*_ : ℕ -> ℕ -> ℕ
-- zero    * n  =  zero
-- (suc m) * n  =  n + (m * n)

-- *-assoc      : ∀ (m n p : ℕ) -> (m * n) * p ≡ m * (n * p)
-- *-distrib-+' : ∀ (m n p : ℕ) -> (m + n) * p ≡ m * p + n * p
-- +-assoc3     : ∀ (m n p : ℕ) -> (m + n) + p ≡ m + (n + p)
*-zero-is-zero : ∀ (n : ℕ) -> n * 0 ≡ 0
*-zero-is-zero zero = refl 
*-zero-is-zero (suc n) = 
  begin 
    (suc n) * 0
  ≡⟨⟩
    0 + (suc n * 0)
  ≡⟨⟩
    (suc n * 0) 
  ≡⟨⟩
    0 + (n * 0)
  ≡⟨ cong (0 +_ ) (*-zero-is-zero n) ⟩
    0 + (0 * n)
  ≡⟨⟩
    0 + 0
  ≡⟨⟩
    0
  ∎

-- todo: *-zero-is-zero' (traditional ind rewrite based proof)
*-zero-is-zero' : ∀ (n : ℕ) -> n * 0 ≡ 0
*-zero-is-zero' zero = refl 
*-zero-is-zero' (suc n) rewrite (*-zero-is-zero n) = refl
-- goal: suc n * 0 ≡ 0 simplies (via the def. to:)
--       0 + (n * 0) ≡ 0 rewrite n * 0 as 0 in goal via ind. hypothesis:(*-zero-is-zero n), 
--       gives: 0 + 0 = refl...
-- so with rewrite, you're always substituting some term key term τ in the goal G
-- based on an extensional equality term of the form lhs ≡ rhs  produced by some 
-- other definition (in the service of constructing evidence of something)
-- .. so  every occurrence of τ in the goal G is substitute by rhs..)

-- _*_ : ℕ -> ℕ -> ℕ
-- zero    * n  =  zero
-- (suc m) * n  =  n + (m * n)

-- *-assoc      : ∀ (m n p : ℕ) -> (m * n) * p ≡ m * (n * p)
-- *-distrib-+' : ∀ (m n p : ℕ) -> (m + n) * p ≡ m * p + n * p
-- +-assoc3     : ∀ (m n p : ℕ) -> (m + n) + p ≡ m + (n + p)
*-succ : ∀ (m n : ℕ) -> m * (suc m) ≡ m + m * n
*-succ zero n = refl
*-succ (suc m) n = 
  begin 
    {!   !}
 
  
*-comm : ∀ (m n : ℕ) -> m * n ≡ n * m 
*-comm n zero = *-zero-is-zero' n
*-comm zero n = sym (*-zero-is-zero' n)
-- *-distrib-+' : ∀ (m n p : ℕ) -> (m + n) * p ≡ m * p + n * p
-- *-comm : ∀ (m n : ℕ) -> m * n ≡ n * m 
-- +-swap : ∀ (m n p : ℕ) -> m + (n + p) ≡ n + (m + p)
*-comm (suc m) n =
  begin
    (suc m) * n 
  ≡⟨⟩
    n + (m * n)
  -- ≡⟨ cong (n +_ ) (+-swap 0 (m * n) 0) ⟩ -- (+-swap 0 (m * n) 0) -> m * n + 0 ≡ m * n + 0
  --  n + (m * n + 0)
  ≡⟨⟩
    {!   !}
  -- (+-swap 0 (m * n) 0) -- gives m + (n + 0) ≡ n + (m + 0)
  -- hmm .. need to get the * in there..
  -- (+-swap n (m * n) 0) -- gives (m * n) + ((n * m) + 0) ≡ (n * m) + ((m * n) + 0)


    -- n + ((m * n) + 0) . using +-swap
-- (+-swap m n 0)
-- goal: n + m * n ≡ n * suc m
-- (+-swap 
    -- cong ( n +_ ) (*-comm n m )
-- n + m * n ≡ n * suc m
-- sym:
-- n * suc m ≡ n + m * n
-- *-comm 
-- (*-distrib-+' zero n zero)

data Bin : Set where 
  ⟨⟩ : Bin 
  _O : Bin → Bin 
  _I : Bin → Bin 

-- inc : Bin -> Bin 
-- inc (⟨⟩ O O O O) = ⟨⟩ O O O I