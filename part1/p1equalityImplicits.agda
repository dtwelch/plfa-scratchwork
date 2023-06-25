module p1EqualityImplicits where

-- called _≡_ in the text (rightly so)
-- so this is a super explicit (indexed) version of the official _≡_
data Equiv {A : Set} : A -> A -> Set where 
    refl : ∀ {x : A} -> Equiv x x 

trans : ∀ {A : Set} (x y z : A)
    -> Equiv x y 
    -> Equiv y z 
    ------------
    -> Equiv x z 
trans x' y' z' refl refl = refl

cong : ∀ {A B : Set} (f : A -> B) {x y : A}
  -> Equiv x y
  --------------------
  -> Equiv (f x) (f y)
cong f refl  =  refl

-- constructing the operators used to do forward chain 
-- reasoning about the Equiv datatype
module Equiv-Reasoning {A : Set} where 
    infix  1 begin_ 
    infixr 2 _equiv⟨⟩_  _equiv⟨_⟩_
    infix  3 _∎

    begin_ : ∀ {x y : A}
        -> Equiv x y 
        ------------
        -> Equiv x y 
    begin_ h = h

    -- asserting two terms of type A are equal
    _equiv⟨⟩_ : ∀ (x : A) {y : A}
        -> Equiv x y 
        -------------
        -> Equiv x y
    _equiv⟨⟩_ x' h1 = h1

    -- justified equivalence
    _equiv⟨_⟩_ : ∀ (x : A) {y z : A}
        -> Equiv x y 
        -> Equiv y z 
        ------------
        -> Equiv x z 
    _equiv⟨_⟩_ x' {y'} {z'} h1 h2 = trans x' y' z' h1 h2
    -- just remember the x' in the pattern could've been called anything
    -- and since {y z : A} are in curly braces, we can't add them to the 
    -- pattern as easily as we can x' (i.e.: we need to say: {y'} {z'})..
    -- I guess this says we're explicitly saying the thing we're introducing
    -- is an implicit variable
    
    _∎ : ∀ (x : A)
        ------------
        -> Equiv x x 
    _∎ x = refl

open Equiv-Reasoning

trans' : ∀ {A : Set} (x y z : A) 
    -> Equiv x y 
    -> Equiv y z 
    ------------
    -> Equiv x z 
trans' x' y' z' xEqy yEqz = 
    begin 
        x'
    equiv⟨ xEqy ⟩ 
        y'
    equiv⟨ yEqz ⟩ 
        z'
    ∎

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

-- again, 'postulate' in agda means 'axiom' (there is no explicit axiom keyword)
postulate
  +-identity    : ∀ (m : ℕ) -> Equiv (m + zero) m
  +-suc         : ∀ (m n : ℕ) -> Equiv (m + suc n) (suc (m + n))

+-comm : ∀ (m n : ℕ) -> Equiv (m + n) (n + m)
+-comm m zero =
    begin 
        m + zero
    equiv⟨ +-identity m ⟩
        m
    equiv⟨⟩ 
        zero + m -- note: no justification needed for this step -- it's due rewrites using
        --  base case of _+_ (this happens automatically as part of definitional equality substs)
        -- (this is why we were able to use normal equiv⟨⟩ that equates a to b -- 
        --  as opposed to the justified version that inserts an extra piece of evidence, p,
        --  that helps convert a to b... i.e: a p b)
    ∎
+-comm m (suc n) = 
    begin 
        m + suc n 
    equiv⟨ +-suc m n ⟩ -- no intermediate proofs needed? 
        suc (m + n)
    equiv⟨ cong suc (+-comm m n) ⟩ -- gives us in context the equality: Equiv suc (m + n) suc (n + m) -- i.e. suc (m + n) ≡ suc (n m)
        suc (n + m)
    equiv⟨⟩ 
        suc n + m 
    ∎

{-
Agda always treats a term as equivalent to its simplified term. 
The reason that one can write:
    suc (n + m)
    ≡⟨⟩
    suc n + m
is because Agda treats both terms as the same. This also means that one could instead 
interchange the lines and write:
    suc n + m
    ≡⟨⟩
    suc (n + m)
and Agda would not object. Agda only checks that the terms separated by ≡⟨⟩ have the same 
simplified form; it’s up to us to write them in an order that will make sense to the 
reader.
-}
    
-- rewriting

data even : ℕ -> Set

data odd  : ℕ -> Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    -> odd n
    ---------------
    -> even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    -> even n
    ---------------
    -> odd (suc n)

{-# BUILTIN EQUALITY Equiv #-}

even-comm : ∀ (m n : ℕ)
    -> even (m + n)
    ---------------
    -> even (n + m)
even-comm  m n ev rewrite +-comm m n = ev
-- h1 : even (m + n)
-- (+-comm m n) : Equiv (m + n) (n + m)
-- so h1 : even (m + n)  rewrite (+-comm m n) introduces the following 
--                       into context: m + n ≡ n + m  ..i.e.: put in our long
--                       form notation Equiv (m + n) (n + m)
-- this allows us to rewrite the goal into:
--   even (n + m) ≡ even (n + m)
-- which is proven via refl

-- multiple rewrites

-- "here is a second proof that addition is commutative, 
-- relying on rewrites rather than chains of equalities.."
+-comm' : ∀ (m n : ℕ) -> Equiv (m + n) (n + m)
+-comm' zero n rewrite +-identity n  = refl
+-comm' (suc m) n rewrite +-suc n m | +-comm' m n  = refl
-- --   +-suc         : ∀ (m n : ℕ) -> Equiv (m + suc n) (suc (m + n))

-- goal: first we have:
--   Equiv (suc m + n) (n + suc m)
--
-- then rewrite it with: rewrite +-suc n m to yield:
--   Equiv (suc (m + n)) (suc (n + m))
--
-- but we still have to flip m and n, so add the commutativity
-- inductive hypothesis (itself an Equivalence/equality term) as a rewrite 
-- that rule allows us to flip the arguments to the top level Equiv .. 

-- base case notes:
-- +-comm' zero n yields a term of type: Equiv (zero + n) (n + zero)
-- rewriting zero + n to be n using the +-identity postulate above.. 
--
-- To summarize:
-- +-comm' zero n : Equiv (zero + n) (n + zero)
-- +-comm' zero n rewrite (+-identity n) : Equiv n n 
--           (where +identity : ∀ (m : ℕ) -> Equiv (m + zero) m)
-- this last exp can be produced/matched via a final refl..

{-
even-comm' : ∀ (m n : ℕ) 
    -> even (m + n) 
    ---------------
    -> even (n + m)
even-comm' m n even with 
-}