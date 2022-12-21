module p1equality where
open import Data.Nat using (ℕ; zero)
-- data _≡_ {A : Set} (x : A) : A -> Set where 
--    refl : x ≡ x 

-- note: above and below (indexed vs parameterized versions)

data _≡_ {A : Set} : A -> A -> Set where
    refl : (a : A) -> a ≡ a
-- refl {ℕ} (0) gives/constructs/provides-evidence-for the term: 0 ≡ 0

infix 4 _≡_


{-
-- yields (for first version of ≡ above)

refl {ℕ} {0} : 0 ≡ 0
refl {ℕ} {1} : 1 ≡ 1
refl {ℕ} {2} : 2 ≡ 2
...
refl {Bool} {true} : true ≡ true
...
refl {Bool} {not b} : not b ≡ not b   -- if 'b : Bool' is a parameter

-}



sym : ∀ {A : Set} (x y : A)
    -> x ≡ y 
    ---------
    -> y ≡ x
sym .a .a (refl a) = refl a

