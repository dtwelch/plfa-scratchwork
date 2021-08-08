module p1c where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

data _⩽_ : ℕ -> ℕ -> Set where
  z⩽n : ∀ (n : ℕ)
      ------------
      -> zero ⩽ n

  s⩽s : ∀ (m n : ℕ)
      -> m ⩽ n
      -------------
      -> suc m ⩽ suc n

-- _ : 2 ⩽ 4
-- _ = s⩽s (s⩽s 0 2 (z⩽n 2))

infix 4 _⩽_

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

-- data Square : ℕ -> Set where
--

-- claim:
-- rt₁ : (n : ℕ) -> Square n -> Nat
-- rt₁ _ (sq m) = m

-- claim:
leq-inv-shorten : ∀ (m n : ℕ)
  -> suc m ⩽ suc n    -- h1
     --------------
  -> m ⩽ n
leq-inv-shorten x y (s⩽s x y h1)  = h1
-- how does it know what hyp2 refers to the last -> m ⩽ n .. I thought
-- I was trying to provide evidence that m ⩽ n

-- hyp2 has to refer to m ⩽ n since the term (s⩽s x y hyp2) evaluates to it..i guess.

 -- claim:
leq-refl : ∀ (n : ℕ)
  ------------------
  -> n ⩽ n
leq-refl zero = z⩽n zero
leq-refl (suc moo) = s⩽s _ _ (leq-refl moo)

-- claim (hint: two defining equations):
leq-trans : ∀ (m n p : ℕ)
  -> m ⩽ n -- hypothesis 1 (h1)
  -> n ⩽ p -- hypothesis 2 (h2)
  -------
  -> m ⩽ p
  -- zero ⩽ n
leq-trans zero y z h1 h2  = z⩽n _
leq-trans (suc x) (suc y) (suc z) (s⩽s x y h1) (s⩽s y z h2) = s⩽s x z (leq-trans x y z h1 h2)

{-
z⩽n : ∀ (n : ℕ)
    ------------
    -> zero ⩽ n

s⩽s : ∀ (m n : ℕ)
    -> m ⩽ n
    -------------
    -> suc m ⩽ suc n
-}
leq-antisym : ∀ (m n : ℕ)
  -> m ⩽ n
  -> n ⩽ m
  ---------
  -> m ≡ n
                    -- constructing evidence for the first part of the claim (after ->) -- i.e.: m ⩽ n
leq-antisym zero zero (z⩽n zero) (z⩽n zero) = refl
leq-antisym (suc x) (suc y) (s⩽s x y h1) (s⩽s y x h2) = cong suc (leq-antisym x y h1 h2)
-- recall cong: in this case, saying cong suc (leq-antisym x y h1 h2)  is
-- applying the successor fn 'suc' to each side of the equation resulting from
-- the app: (leq-antisym x y h1 h2)

data Total : ℕ -> ℕ -> Set where
  forward : ∀ (m n : ℕ)
          -> m ⩽ n
          -------------
          -> Total m n

  flipped : ∀ (m n : ℕ)
          -> n ⩽ m
          -------------
          -> Total m n

⩽-total : ∀ (m n : ℕ) -> Total m n
⩽-total zero n             = forward zero n (z⩽n n)
⩽-total (suc x) zero       = flipped (suc x) zero (z⩽n (suc x))
⩽-total (suc x) (suc y) with ⩽-total x y
...                        | forward x y h1  =  forward (suc x) (suc y) (s⩽s x y h1) -- forward case of ind. hypo
...                        | flipped x y h2  =  flipped (suc x) (suc y) ((s⩽s y x) h2) -- flipped case of ind, hypo

+-right-mono-wrt-⩽ : ∀ (n p q : ℕ)
  -> p ⩽ q
  -------------
  -> n + p ⩽ n + q
+-right-mono-wrt-⩽ zero    p q h1   = h1
+-right-mono-wrt-⩽ (suc x) y z h2   = s⩽s (x + y) (x + z) (+-right-mono-wrt-⩽ x y z h2)
                                          -- if you don't do (x + y) (x + z)
                                          -- and just instantiate it with x y, it (rightly)
                                          -- doesn't prove


-- commutative is for + and any other binary operater that happens to have
-- that property. If we're talking
-- about binary relations, we say a binary relation relation is
-- symmetric (as opposed to commutative, though technically the line is blurred; Has to
-- has do with the codomain of the function or relation being looked at. In the
-- case of a relation this happens to always be the set B.


-- +-comm' : ∀ (m n : ℕ) -> m + n ≡ n + m

+-left-mono-wrt-⩽ : ∀ (m n p : ℕ)
  -> m ⩽ n    -- h1
  ----------
  -> m + p ⩽ n + p
+-left-mono-wrt-⩽ x y z h1 rewrite
  (+-comm' x z) | (+-comm' y z) = +-right-mono-wrt-⩽ z x y h1

-- x + z ⩽ y + z
-- apply +-comm' x z
-- z + x ⩽ y + z
-- apply +-comm' y z
-- z + x ⩽ z + y
--  =
-- +-right-mono-wrt-⩽ z y x h1 [gives: z + x ⩽ z + y]
-- (this is how we construct a term with 'type' z + x ⩽ z + y)

-- now we can combine the left and right results:

-- +-left-mono-wrt-⩽  : ∀ (m n p : ℕ) -> m ⩽ n -> m + p ⩽ n + p
-- +-right-mono-wrt-⩽ : ∀ (n p q : ℕ) -> p ⩽ q -> n + p ⩽ n + q
-- leq-trans : ∀ (m n p : ℕ) -> m ⩽ n -> n ⩽ p -> m ⩽ p

+-mono-⩽ : ∀ (m n p q : ℕ)
  -> m ⩽ n  -- h1
  -> p ⩽ q  -- h2
  ---------
  -> m + p ⩽ n + q
+-mono-⩽ i j k l h1 h2 =
  leq-trans (i + k) (j + k) (j + l) -- ((i + k) ⩽ (j + k)) -> ((j + k) ⩽ (j + l)) -> (i + k) ⩽ (j + l)
    (+-left-mono-wrt-⩽ i j k h1) -- i + k ⩽ j + k
    (+-right-mono-wrt-⩽ j k l h2)   -- j + k ⩽ j + 1
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
-- suc (suc m) ⩽ suc n
lt-inv-shorten : ∀ (m n : ℕ)
  -> suc m < suc n    -- h1
     --------------
  -> m < n
lt-inv-shorten x y (s<s x y h1) = h1

<-suc1' : ∀ (m n : ℕ)
  -> suc m ⩽ n   -- h1
  -------------
  -> m < n
<-suc1' zero (suc y) h1 = z<s y
<-suc1' (suc x) (suc y) (s⩽s (suc x) y h1) = s<s x y (<-suc1' x y h1)
-- note (as mentioned below): on lhs of the = above, the (s⩽s (suc x) y h1)
-- is constructing a term that is the same shape as the one for the
-- ind. hypothesis h1 in the type signature of the claim. If the shape doesn't
-- need to be tweaked for whatever we are attempting to prove, we could've just
-- written the lhs of the = above as (suc x) (suc y) h1 but this would've made
-- h1 a term with the (incorrect) shape (suc (suc m)) ⩽ (suc n)

<-suc2' : ∀ (m n : ℕ)
  -> m < n    -- h1
  -------------
  -> suc m ⩽ n
<-suc2' zero (suc y) h1 = s⩽s zero y (z⩽n y)
<-suc2' (suc x) (suc y) (s<s x y h1) = s⩽s (suc x) y (<-suc2' x y h1)
-- So I think the (s<s x y h1) on the lhs of = is like the inductive hypothesis...
-- i.e.: you're constructing a term that is the claim for the nth element
-- of whatever sequence you're dealing with -- so you're just it seems constructing
-- a term of the *right shape* and providing it as "pattern evidence" (in this case h1) that in
-- some sense is assumed (this is like the inductive argument: we can
-- assume it for the nth element, and we show that it holds as well for the
-- n + 1 element.

{-
leq-trans : ∀ (m n p : ℕ)
  -> m ⩽ n -- hypothesis 1 (h1)
  -> n ⩽ p -- hypothesis 2 (h2)
  -------
  -> m ⩽ p
-}

<-trans : ∀ (m n p : ℕ)
  -> m < n    -- h1
  -> n < p    -- h2
  ----------
  -> m < p
-- base case goal: zero < suc p
<-trans zero (suc n) (suc p) h1 h2 = z<s p
-- ind. case goal: suc m < suc p
<-trans (suc m) (suc n) (suc p) (s<s m n h1) (s<s n p h2) =
  s<s m p (<-trans m n p h1 h2)
