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

-- transitivity of Equiv
trans : ∀ {A : Set} (x y z : A) 
    -> Equiv x y 
    -> Equiv y z 
    ------------
    -> Equiv x z 
trans x y z (refl x _) (refl y _) = refl x x
-- note: could've also done (refl x _) for both -- including (refl z _)

-- refl x provides evidence that Equiv(x, x) and is passed into trans
-- as the first piece of evidence/hypothesis... but doing so 
-- implies that y must equal x  (that's why y = x shows up in the context)

-- applying refl again produces a term that forces z and x 
-- to be the same (otherwise it couldn't be used as a hypothesis)..
-- correspondingly z = x is added to the context (y = x is still there)

-- in order to match the y in the first '-> Equiv x y'

-- congruence
cong : ∀ {A B : Set} (f : A -> B) (x y : A)
    -> Equiv x y 
    --------------
    -> Equiv (f x) (f y)
cong f' x' y' (refl x' _) = (refl (f' x') (f' x')) 

cong-app : ∀ {A B : Set} (f g : A -> B)
    -> Equiv f g 
    ---------------------------------
    -> ∀ (x : A) -> Equiv (f x) (g x)
cong-app f' g' (refl f' _) x = (refl (f' x) (f' x))

-- the refl above creates evidence that forces f' and g' to
-- be considered ≡ fns in the context

module Equiv-Reasoning {A : Set} where 
    infix  1 begin_ 
    -- infixr 2 _Equiv⟨⟩_   _Equiv⟨_⟩_
   -- infix  3 _∎

    begin_ : ∀ (x y : A)
        -> Equiv x y 
        ------------
        -> Equiv x y 
    begin_ x' y' h = h