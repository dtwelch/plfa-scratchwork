module p1isomorphism where

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
    -> (∀ (x : A) -> f x ≡ g x)
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



-- +-comm : ∀ (m n : ℕ) -> (m + n) ≡ (n + m)
-- +-suc  : ∀ (m n : ℕ) -> m + suc n ≡ suc (m + n)

-- helper fn:
helper : ∀ (m n : ℕ) -> m +' n ≡ n + m
helper m zero =  refl  -- m + zero or m +' zero both match the base case and simplification happens to get m ≡ m 
helper m (suc n) = cong suc (helper m n) 

-- we want a theorem to show that _+_ and _+'_ (defined above) always
-- give back the same result given the same arguments (see above para for proof via helper lemma idea)
same-app : ∀ (m n : ℕ) → m +' n ≡ m + n
same-app m n rewrite +-comm m n = helper m n


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


-- NOTE: not currently typechecking due to the fact that the quantified 
-- function vars f and g are not marked as implicit parameters.. i.e.:
--    extensionality : ∀ {A B : Set} (f g : A -> B)
-- vs:
--    extensionality : ∀ {A B : Set} {f g : A -> B} -- in this ver. the typechecking works 
-- going to try to do it in the explicit way (passing in _+_, etc)
--same : _+'_ ≡ _+_  
--same = {!   !}

same : _+'_ ≡ _+_
same = extensionality (_+'_) (_+_) (λ x -> extensionality (_+'_ x) (_+_ x) ({!   !}))
--extensionality (λ m → extensionality {!(λ n → ?)!})
-- ?0 : (x : ℕ) → (m +' x) ≡ m + x
-- ------------
--extensionality (λ x -> extensionality {!?!} )
--?0 : (x₁ : ℕ) → (x +' x₁) ≡ x + x₁  -- so it is a fn...

-- in the explicit version, you need to partially apply the outer λ to account for needing to 
-- apply functions f and g in a curried way this is why we do: extensionality (_+'_ x) (_+_ x) 
-- instead of just: extensionality (_+'_) (_+_) -- we already did that over the outermost extensionality
-- app 

-- extensionality (_+'_) (_+_) (λ x -> extensionality (_+'_) (_+_) (λ y -> same-app x y))

