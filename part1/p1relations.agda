module p1relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

data _≤_ : ℕ -> ℕ -> Set where
  z≤n : ∀ (n : ℕ)
      ------------
      -> zero ≤ n

  s≤s : ∀ (m n : ℕ)
      -> m ≤ n
      -------------
      -> suc m ≤ suc n

-- _ : 2 ⩽ 4
-- _ = s⩽s (s⩽s 0 2 (z⩽n 2))

infix 4 _≤_

inv-s≤s : ∀ (m n : ℕ)
    -> suc m ≤ suc n  -- h1
       --------------
    -> m ≤ n 
inv-s≤s zero n h1 = (z≤n n) -- <-- technically not needed...
inv-s≤s m n (s≤s m n h1) = h1

inv-z≤n : ∀ (m : ℕ)
  ->  m ≤ zero 
      --------
  ->  m ≡ zero
inv-z≤n m (z≤n m) = refl

-- exercise:
-- Give an example of a preorder that is not a partial order.
-- fixing a domain (vertex set)
-- V = {a, b, c, d}
-- E = {(a, b), (b, c) (c, d)}
-- G = (V, E)

-- Is_Connected_to_In_G : V x V -> Bool
--  a Is_Connected_to_In_G a (reflexivity)
--  b Is_Connected_to_In_G b (reflexivity)
--  etc.

--  if a Is_Connected_to_In_G b and  
--     b Is_Connected_to_In_G c then 
--     a Is_Connected_to_In_G c (transitivity)

-- so reln 'Is_Connected_to_In_G' is a preordering
-- is it anti-symmetric? no. 
-- 
-- Consider:
--  a Is_Connected_to_In_G c and c Is_Connected_to_In_G a is true,
--  but it is not the case that a = c (diff nodes), so the
--  Is_Connected_to_In_G is an example of a relation that is a 
--  preordering, but not a partial order.

≤-refl : ∀ (n : ℕ)
     -------
    -> n ≤ n 
≤-refl zero = (z≤n zero)  
≤-refl (suc x) = (s≤s x x (≤-refl x))


≤-trans : ∀ (m n p : ℕ)
    -> m ≤ n -- h1
    -> n ≤ p -- h2
    --------
    -> m ≤ p 
≤-trans zero m p h1 h2 =  (z≤n p)
≤-trans (suc m) (suc n) (suc p) (s≤s m n h1) (s≤s n p h2) = s≤s m p (≤-trans m n p h1 h2) 

-- note: need to say (s≤s m n h1), etc. to construct evidence for the ind cases hypotheses
-- (due to our instantiation of (suc m), (suc n), and (suc p) to the 
--  left of the = in the ind. case)

≤-antisym : ∀ (m n : ℕ) 
    -> m ≤ n 
    -> n ≤ m  
    ---------
    -> m ≡ n
≤-antisym zero n (z≤n n) h2 = sym (inv-z≤n n h2)
≤-antisym (suc m) (suc n) h1 h2 = 
    cong suc (≤-antisym m n (inv-s≤s m n h1) (inv-s≤s n m h2) ) 

leq-inv-shorten : ∀ (m n : ℕ)
  -> suc m ≤ suc n    -- h1
     --------------
  -> m ≤ n
leq-inv-shorten x y (s≤s x y h1)  = h1

 -- claim:
leq-refl : ∀ (n : ℕ)
  ------------------
  -> n ≤ n
leq-refl zero = z≤n zero
leq-refl (suc moo) = s≤s _ _ (leq-refl moo)

-- claim (hint: two defining equations):
leq-trans : ∀ (m n p : ℕ)
  -> m ≤ n -- hypothesis 1 (h1)
  -> n ≤ p -- hypothesis 2 (h2)
  -------
  -> m ≤ p
  -- zero ≤ n
leq-trans zero y z h1 h2  = z≤n _
leq-trans (suc x) (suc y) (suc z) (s≤s x y h1) (s≤s y z h2) = s≤s x z (leq-trans x y z h1 h2)

{-
z≤n : ∀ (n : ℕ)
    ------------
    -> zero ≤ n

s≤s : ∀ (m n : ℕ)
    -> m ≤ n
    -------------
    -> suc m ≤ suc n
-}
leq-antisym : ∀ (m n : ℕ)
  -> m ≤ n
  -> n ≤ m
  ---------
  -> m ≡ n
                    -- constructing evidence for the first part of the claim (after ->) -- i.e.: m ⩽ n
leq-antisym zero zero (z≤n zero) (z≤n zero) = refl
leq-antisym (suc x) (suc y) (s≤s x y h1) (s≤s y x h2) = cong suc (leq-antisym x y h1 h2)
-- recall cong: in this case, saying cong suc (leq-antisym x y h1 h2)  is
-- applying the successor fn 'suc' to each side of the equation resulting from
-- the app: (leq-antisym x y h1 h2)

data Total : ℕ -> ℕ -> Set where
  forward : ∀ (m n : ℕ)
          -> m ≤ n
          -------------
          -> Total m n

  flipped : ∀ (m n : ℕ)
          -> n ≤ m
          -------------
          -> Total m n

≤-total : ∀ (m n : ℕ) -> Total m n
≤-total zero n             = forward zero n (z≤n n)
≤-total (suc x) zero       = flipped (suc x) zero (z≤n (suc x))
≤-total (suc x) (suc y) with ≤-total x y
...                        | forward x y h1  =  forward (suc x) (suc y) (s≤s x y h1) -- forward case of ind. hypo
...                        | flipped x y h2  =  flipped (suc x) (suc y) ((s≤s y x) h2) -- flipped case of ind, hypo

+-right-mono-wrt-≤ : ∀ (n p q : ℕ)
  -> p ≤ q
  -------------
  -> n + p ≤ n + q
+-right-mono-wrt-≤ zero    p q h1   = h1
+-right-mono-wrt-≤ (suc x) y z h2   = s≤s (x + y) (x + z) (+-right-mono-wrt-≤ x y z h2)
                                          -- if you don't do (x + y) (x + z)
                                          -- and just instantiate it with x y, it (rightly)
                                          -- doesn't prove


-- +-comm' : ∀ (m n : ℕ) -> m + n ≡ n + m

+-left-mono-wrt-≤ : ∀ (m n p : ℕ)
  -> m ≤ n    -- h1
  ----------
  -> m + p ≤ n + p
+-left-mono-wrt-≤ x y z h1 rewrite
  (+-comm x z) | (+-comm y z) = +-right-mono-wrt-≤ z x y h1

-- x + z ≤ y + z
-- apply +-comm' x z
-- z + x ≤ y + z
-- apply +-comm' y z
-- z + x ≤ z + y
--  =
-- +-right-mono-wrt-⩽ z y x h1 [gives: z + x ≤ z + y]
-- (this is how we construct a term with 'type' z + x ≤ z + y)

-- now we can combine the left and right results:

-- +-left-mono-wrt-≤  : ∀ (m n p : ℕ) -> m ≤ n -> m + p ≤ n + p
-- +-right-mono-wrt-≤ : ∀ (n p q : ℕ) -> p ≤ q -> n + p ≤ n + q
-- leq-trans : ∀ (m n p : ℕ) -> m ≤ n -> n ≤ p -> m ≤ p

+-mono-⩽ : ∀ (m n p q : ℕ)
  -> m ≤ n  -- h1
  -> p ≤ q  -- h2
  ---------
  -> m + p ≤ n + q
+-mono-⩽ i j k l h1 h2 =
  leq-trans (i + k) (j + k) (j + l) -- ((i + k) ⩽ (j + k)) -> ((j + k) ⩽ (j + l)) -> (i + k) ⩽ (j + l)
    (+-left-mono-wrt-≤ i j k h1) -- i + k ⩽ j + k
    (+-right-mono-wrt-≤ j k l h2)   -- j + k ⩽ j + 1
-- goal: i + k ⩽ j + l
-- phew.

*-id' : ∀ (n : ℕ)
        -----------
        -> n * zero ≡ zero
*-id' zero = refl
*-id' (suc x) rewrite *-id' x = refl
--  want to do 'rewrite' on results where ≡ is involved I think...

{-
_*_ : Nat → Nat → Nat
zero  * m = zero
suc n * m = m + n * m
-}
-- +-suc' : ∀ (m n : ℕ) -> m + suc n ≡ suc (m + n)
-- +-comm' : ∀ (m n : ℕ) -> m + n ≡ n + m
-- +-assoc' : ∀ (m n p : ℕ) -> (m + n) + p ≡ m + (n + p)
{-*-suc' : ∀ (m n : ℕ ) -> m * suc n ≡ m + m * n  -- needed for *-mono' (I think), regardless, got stuck..
*-suc' zero n =
  begin
    zero * suc n
  ≡⟨⟩
    zero
  ∎
*-suc' (suc m) n =
  begin
    suc m * suc n -- by ind. hypothesis for *, we have:  m * suc n ≡ m + m * n
  ≡⟨⟩
    ?
-}

infix 4 _<_

-- the relation less than has an infinite number of
-- instances... 0 < 1, 0 < 2, 1 < 2, etc.
-- we can write a finite datatype that encompasses all of
-- these instances with just a few inference rules (or: constructors..)
data _<_ : ℕ -> ℕ -> Set where
  z<s : ∀ (n : ℕ)
      ------------
      -> zero < suc n

  s<s : ∀ (m n : ℕ)
      -> m < n
      --------------
      -> suc m < suc n

{-
z⩽n : ∀ (n : ℕ)
    ------------
    -> zero ⩽ n

s⩽s : ∀ (m n : ℕ)
    -> m ⩽ n
    -------------
    -> suc m ⩽ suc n

-}
-- this is the evidence we need to provide in order to use the ind. hypo:
-- suc (suc m) ≤ suc n
lt-inv-shorten : ∀ (m n : ℕ)
  -> suc m < suc n    -- h1
     --------------
  -> m < n
lt-inv-shorten x y (s<s x y h1) = h1

<-suc1' : ∀ (m n : ℕ)
  -> suc m ≤ n   -- h1
  -------------
  -> m < n
<-suc1' zero (suc y) h1 = z<s y
<-suc1' (suc x) (suc y) (s≤s (suc x) y h1) = s<s x y (<-suc1' x y h1)
-- note (as mentioned below): on lhs of the = above, the (s⩽s (suc x) y h1)
-- is constructing a term that is the same shape as the one for the
-- ind. hypothesis h1

<-suc2' : ∀ (m n : ℕ)
  -> m < n    -- h1
  -------------
  -> suc m ≤ n
<-suc2' zero (suc y) h1 = s≤s zero y (z≤n y)
<-suc2' (suc x) (suc y) (s<s x y h1) = s≤s (suc x) y (<-suc2' x y h1)
-- So I think the (s<s x y h1) on the lhs of = is like the inductive hypothesis...
-- i.e.: you're constructing a term that is the claim for the nth element
-- of whatever sequence you're dealing with -- so you're just it seems constructing
-- a term of the *right shape* and providing it as "pattern evidence" (in this case h1) that in
-- some sense is assumed (this is like the inductive argument: we can
-- assume it for the nth element, and we show that it holds as well for the
-- n + 1 element.
-- that the n + 1th element holds as well..



-- s≤s (suc x) (suc y) (<-suc2' x y
-- goal: suc (suc x) ⩽ suc y

{-
--_+'_ : N' ->  N' ->  N'
--zero +' n = n
--(suc m) +' n = suc (m +' n)
--infixl 30 _+'_
-}
-- C-c C-q  (Quit, kill the Agda process, clear pending goals ...)
-- C-c C-c      (in a hole split -- or show goal)
-- C-c C-t      (show type for current hole)
-- C-c C-d      (show type of a definition -- like 'cong' -- for congruence)
-- https://agda.readthedocs.io/en/v2.6.2.2/getting-started/a-taste-of-agda.html
-- good tutorial showing you the steps and tools you can
-- use to go about this proof
 
-- data Total' (m n : ℕ) : Set where 
data Total' : ℕ -> ℕ -> Set where 
  fwd : ∀ (m n : ℕ) 
    -> m ≤ n 
    -------------
    -> Total' m n

  flp : ∀ (m n : ℕ) 
    -> n ≤ m 
    -------------
    -> Total' m n

≤-total' : ∀ (m n : ℕ) -> Total' m n 
≤-total' zero n = fwd zero n (z≤n n)
≤-total' (suc m) zero =  (flp (suc m) zero) ( z≤n (suc m) ) 
≤-total' (suc m) (suc n) = {!   !}