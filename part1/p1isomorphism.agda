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
-- (using extensionality thm)

cong-app' : ∀ {A B : Set} {f g : A -> B}
    -> f ≡ g
    ---------------------
    -> ∀ (x : A) -> f x ≡ g x
cong-app' refl v = refl
-- instantiating hypothesis 1 w/ refl makes f ≡ f for 
-- the rest of the context (then you get (x : A) -> f x ≡ f x) then 
-- add some var: v as the last pattern var and the goal becomes:
-- f v ≡ f v (which can be discharged via refl)

-- +-comm : ∀ (m n : ℕ) -> (m + n) ≡ (n + m)
-- helper fn:
helper : ∀ (m n : ℕ) -> m +' n ≡ n + m
helper m zero =  refl  -- m + zero or m +' zero both match the base case and simplification happens to get m ≡ m 
helper m (suc n) = {!   !}

-- extensionality (_+_) (_+'_) : ((x : ℕ) -> _+_ x ≡ _+'_ x) -> _+_ ≡ _+'_

-- equating results of applications for different plus operators: _+'_ and _+
same-app : ∀ (m n : ℕ) -> m +' n ≡ m + n
-- now to prove it via rewrite
same-app m n rewrite +-comm m n = {!   !}

-- same-app m n = ?                    -- goal: (m +' n) ≡ m + n 
-- same-app m n rewrite +-comm m n = ? -- goal: (m +' n) ≡ n + m (flips m and n on rhs)



-- extensionality (_+_) (_+'_) produces ((x : ℕ) -> _+_ x ≡ _+'_ x) -> _+_ ≡ _+'_

-- extensionality (_+_) (_+'_) (λ v -> (m + v) ≡ (m +' v)) ??