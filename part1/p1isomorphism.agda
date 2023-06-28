import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

-- composition
_∘_ : ∀ {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)
(g ∘ f) x  = g (f x)

-- can also do it this way:
_∘'_ : ∀ {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)
g ∘' f  =  λ x -> g (f x)

-- extensionality
postulate 
    extensionality : ∀ {A B : Set} (f g : A -> B)
        -> (∀ (x : A) -> f x ≡ g x )
        ----------------------------
        -> f ≡ g

-- ".. consider that we need results from two libraries, one where addition is 
--  defined, as in Chapter Naturals, and one where it is defined the other way 
--  around."
-- 
-- Note: normal _+_ operator defines the patterns different (case patterns flipped):
-- _+_ : ℕ → ℕ → ℕ
-- zero + n = n                -- base case
-- (suc m) + n = suc (m + n)   -- ind hypo

_+'_ : ℕ -> ℕ -> ℕ
m +' zero = m 
m +' (suc n) = suc (m +' n)

-- we want a theorem to show that _+_ and _+'_ (defined above) always
-- give back the same result given the same arguments

cong-app' : ∀ {A B : Set} {f g : A -> B}
    -> f ≡ g
    ---------------------
    -> ∀ (x : A) -> f x ≡ g x
cong-app' refl v = refl
-- instantiating hypothesis 1 w/ refl forces f ≡ f for 
-- the rest of the context .. so we've satisfied the f ≡ g part..
-- then, when dealing w/ the ∀ part: 
-- (x : A) -> f x ≡ f x
-- you add some var, v, as the last pattern var and the goal subsequently 
-- becomes:
-- f v ≡ f v (which can be discharged via refl)

-- already imported (hence the prime on the name)
cong' : ∀ {A B : Set} (f : A -> B) {x y : A}
    -> x ≡ y
    ------------
    -> f x ≡ f y
cong' f refl  =  refl

-- +-comm : ∀ (m n : ℕ) -> (m + n) ≡ (n + m)
-- +-suc  : ∀ (m n : ℕ) -> m + suc n ≡ suc (m + n)

-- helper fn:
helper : ∀ (m n : ℕ) -> m +' n ≡ n + m
helper m zero =  refl  -- m + zero or m +' zero both match the base case and simplification happens to get m ≡ m 
helper m (suc n) = cong suc (helper m n) 

-- some details on proof for 'helper' constant above: 

-- the right hand side (above) beginning with 'cong' constructs a term that has the following 
-- as its type^*:
--  (m +' suc n) ≡ suc n + m
-- so we need to construct a term of this general shape ^*OR one definitionally equal 
-- via ≡ (based on the way its constructor defined in the datatype). Start w/ ind. hypothesis
--   helper m n 
-- which produces a term of rougly the shape of the goal .. i.e.: an ≡-term w/ an app of _+'_ 
-- as the top level subterm of the lhs and an app of _+_ on the rhs. Here is the term
-- that results from the ind. hypothesis app (helper m n):
--   (m +' n) ≡ n + m
-- now it just needs to get 'turned/transformed' into the goal: (m +' suc n) ≡ suc n + m..
-- This is done via:
--   cong suc (helper m n)
-- cong applies the provided fn (in this case, suc(·)) to the evidence produced by 
-- the inductive hypothesis to produce a term seemingly different (but VERY) close to 
-- the goal: 
--   (m +' suc n) ≡ suc (n + m)    -- this is the goal type
--   suc (m +' n) ≡ suc (n + m)    -- this type results from: cong suc (helper m n)
-- these two terms actually match (see how _+'_ ind. case below):
--   x +' (suc y) = suc (x +' y)   -- ind. case of _+'_ .. (using x and y instead of m n)
-- ..
-- so the term that results from cong suc (helper m n) is definitionally equal to the goal.

-- remember: same-app m n leaves us with a type: m +' n ≡ m + n, which we rewrite using +-comm m n
same-app : ∀ (m n : ℕ) -> m +' n ≡ m + n
same-app m n rewrite +-comm m n = helper m n

-- better to assert that the two operators are actually indistinguishable. This
-- we can do via two applications of extensionality:

same : _+'_ ≡ _+_  
same = extensionality (_+'_) (_+_) {! λ x λ y -> same-app x y  !}
-- extensionality op1 op2 