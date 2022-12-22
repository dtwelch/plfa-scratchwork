module p1equality where
open import Data.Nat using (ℕ; zero)
data _≡_ {A : Set} (x : A) : A -> Set where 
    refl : x ≡ x 

-- note: above and below (indexed vs parameterized versions)

-- data _≡_ {A : Set} : A -> A -> Set where
--    refl : (a : A) -> a ≡ a
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
sym b a refl = refl

-- ok, for an explanation of why refl works above,
-- see: https://cs.uwaterloo.ca/~plragde/747/notes/Equality.html
{-
7.1 Equality is an equivalence relation

There is only one constructor for equality, refl, so 
when we case-split on an equality, Agda will try to 
make the two sides equal through a process known as 
unification. This does not always succeed. 
For simple cases, such as an equality of the form 
y ≡ z, where y and z are variables, Agda will replace 
occurrences of z with y in the goal and context. 
In effect, it is doing a simple rewrite. 
But if y and z are replaced by expressions of even 
modest complexity, unification will often fail 
(the kind of problem it is trying to solve is 
undecidable in general).
-}
