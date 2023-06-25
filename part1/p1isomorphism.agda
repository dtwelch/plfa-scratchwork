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

-- equating results of applications for different plus operators: _+'_ and _+
same-app : ∀ (m n : ℕ) -> m +' n ≡ m + n
-- now to prove it via rewrite
same-app m n = ?