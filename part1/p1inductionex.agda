module p1inductionex where 

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

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