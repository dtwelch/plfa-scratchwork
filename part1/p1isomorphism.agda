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
-- then, when dealing w/ the ∀ you get part w/ ty term: 
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
helper m (suc n) = {!   !}

-- applying the inductive hypothesis, assume helper m n holds ...
-- we use this to construct a term of rougly the shape of the goal
-- ..this gives us an initial term to work with where the left hand 
--  side of the ≡ is _+'_ while the right contains an app of _+_ 
-- (this is high level shape of the term we need to build in order to
--  match the goal)



-- suc (m +' n) ≡ suc (n + m)

-- goal: (m +' suc n) ≡ suc n + m
--
-- +-comm m n
--
-- where +-comm : ∀ (m n : ℕ) -> (m + n) ≡ (n + m)
-- gives:
-- 

-- from one of this shape: (m +' suc n) ≡ suc n + m 
-- commutativity

-- somehow get the suc on the outside of the lhs and rhs of the goal (then apply cong' which equates the arguments of


-- 
-- extensionality (_+_) (_+'_) : ((x : ℕ) -> _+_ x ≡ _+'_ x) -> _+_ ≡ _+'_

-- equating results of applications for different plus operators: _+'_ and _+
same-app : ∀ (m n : ℕ) -> m +' n ≡ m + n
-- now to prove it via rewrite
same-app m n rewrite +-comm m n = {!   !}

-- same-app m n = ?                    -- goal: (m +' n) ≡ m + n 
-- same-app m n rewrite +-comm m n = ? -- goal: (m +' n) ≡ n + m (flips m and n on rhs)



-- extensionality (_+_) (_+'_) produces ((x : ℕ) -> _+_ x ≡ _+'_ x) -> _+_ ≡ _+'_

-- extensionality (_+_) (_+'_) (λ v -> (m + v) ≡ (m +' v)) ??