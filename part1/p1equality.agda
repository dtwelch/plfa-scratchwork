module p1equality where

-- data _≡_ {A : Set} (x : A) : A -> Set where 
--    refl : x ≡ x 

-- note: above and below (indexed vs parameterized versions)

data _≡_ {A : Set} : A -> A -> Set where
    refl : (a : A) -> a ≡ a

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


infix 4 _≡_

sym : ∀ {A : Set} (x y : A)
    -> x ≡ y 
    ---------
    -> y ≡ x
sym b a   = {!   !}

