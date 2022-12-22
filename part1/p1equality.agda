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
-- so the above works when supplied
-- with refl as evidence since some 
-- 'unification' process when refl is
-- applied above ends up triggering an 
-- automatic rewrite/simplification of 
-- the goal and context (given) into:
-- b ≡ b -> b ≡ b
-- (imagine y being substituted for x in the defn)

-- for an explanation of why refl works above,
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

trans : ∀ {A : Set} (x y z : A)
    -> x ≡ y 
    -> y ≡ z 
    --------
    -> x ≡ z 
trans a .a c refl h2 = h2 

-- so the a .a renaming on the case split
-- above is an indication that agda relealized
-- no matter the instantiation for 
-- x and y, they are going to be the same.
-- (some unification algorithm to recognize )

-- equality satisfies congruence: if two terms t1, t2
-- are equal, then they are also equal after application
-- of some function f to both terms
cong : ∀ {A B : Set} (f : A -> B) (x y : A)
    -> x ≡ y 
    ---------
    -> f x ≡ f y 
cong f b a refl = refl

cong₂ : ∀ {A B C : Set} 
          (f : A -> B -> C) 
          (u x : A) (v y : B)
    -> x ≡ u 
    -> y ≡ v 
    ----------------
    -> f u v ≡ f x y
cong₂ f a b i j refl refl = refl