module p1equality where

-- called _≡_ in the text (rightly so)
-- so this is a super explicit (indexed) version of the official _≡_
data Equiv {A : Set} : A -> A -> Set where 
    refl : ∀ (x y : A) -> Equiv x x 

-- note: above and below (indexed vs parameterized versions)

-- data _≡_ {A : Set} : A -> A -> Set where
--    refl : (a : A) -> a ≡ a
-- refl {ℕ} (0) gives/constructs/provides-evidence-for the term: 0 ≡ 0

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
    -> Equiv x y 
    -------------
    -> Equiv y x
sym z y (Equiv.refl z _) = Equiv.refl z z
-- sym x y : Equiv x y → Equiv y x
-- so if we pass in refl as the next arg in the pattern, we force the y already instantiated
-- to be treated as an x..

-- sym x y e = {!   !} -- gives type: Equiv x y (due to the fact we instantiated sym (applied) x and then y)
-- sym has tpe : ∀ {A : Set} (x y : A) -> x ≡ y -> y ≡ x 

trans : ∀ {A : Set} (x y z : A) 
    -> Equiv x y 
    -> Equiv y z 
    ------------
    -> Equiv x z 
trans x y z (refl x _) = {!   !} 