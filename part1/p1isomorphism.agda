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
-- Note: normal _+_ operator defines the patterns different:
--  m + zero for base case, m + (suc n) for ind. case
_+'_ : ℕ -> ℕ -> ℕ
zero +' n = n 
(suc m) +' n = suc (m + n)

-- we want a theorem to show that _+_ and _+'_ (defined above) always
-- give back the same result given the same arguments 
-- (using extensionality thm)

-- +-comm : ∀ (m n : ℕ) -> (m + n) ≡ (n + m)



-- equating results of applications for different plus operators: _+'_ and _+
same-app : ∀ (m n : ℕ) -> m +' n ≡ m + n
-- now to prove it via rewrite
same-app m n rewrite +-comm m n = {!   !}

-- same-app m n = ?                    -- goal: (m +' n) ≡ m + n 
-- same-app m n rewrite +-comm m n = ? -- goal: (m +' n) ≡ n + m (flips m and n on rhs)

cong' : ∀ {A B : Set} (f : A -> B) {x y : A}
    -> x ≡ y
    ------------
    -> f x ≡ f y
cong' f refl  =  refl

cong-app' : ∀ {A B : Set} {f g : A -> B}
    -> f ≡ g
    ---------------------
    -> ∀ (x : A) -> f x ≡ g x
cong-app' refl v = refl
-- instantiating hypothesis 1 w/ refl makes f ≡ f for 
-- the rest of the context (then you get (x : A) -> f x ≡ f x) then 
-- add some var: v as the last pattern var and the goal becomes:
-- f v ≡ f v (which can be discharged via refl)

-- helper fn:
helper : ∀ (m n : ℕ) -> m +' n ≡ m + n 
helper m n = {!   !}

-- extensionality (_+_) (_+'_) produces ((x : ℕ) -> _+_ x ≡ _+'_ x) → _+_ ≡ _+'_