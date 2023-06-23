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
    infix  1 bgn_ 
    infixr 2 _equiv⟨⟩_   _equiv⟨_⟩_
    infix  3 _∎

-- constructing the operators used to do forward chain 
-- reasoning about the Equiv datatype
    bgn_ : ∀ (x y : A)
        -> Equiv x y 
        ------------
        -> Equiv x y 
    bgn_ x' y' h = h

    -- asserting two are equal 
    -- (ver. where no justification evidence/term of type A 
    --  is needed: ⟨⟩)
    _equiv⟨⟩_ : ∀ (x : A) (y : A)
        -> Equiv x y 
        -------------
        -> Equiv x y
    _equiv⟨⟩_ x' y' (refl x _) = refl x x

    -- asserting two are equal 
    -- justification evidence/term provided upon application --
    -- within the: ⟨_⟩ 
    _equiv⟨_⟩_ : ∀ (x : A) (y z : A)
        -> Equiv x y  -- h1
        -> Equiv y z  -- h2
        -------------
        -> Equiv x z 
    -- _Equiv⟨_⟩_ x' y' z' h1 h2 = trans x' y' z' (_Equiv⟨⟩_ x' y' h1) (_Equiv⟨⟩_ y' z' h2)
    -- this way is much shorter and to the point:
    _equiv⟨_⟩_ x' y' z' h1 h2 = trans x' y' z' h1 h2 
    -- h1 and h2 are already in exactly the form we need

    _∎ : ∀ (x : A)
        -------------
        -> Equiv x x
    x ∎  =  (refl x x)

-- NOTE: important that trans' is outdented 
-- (otherwise type A gets shadowed by the module level 
--  type param -- also called A -- and spooky stuff starts 
--  happening i.e.: types start getting subscripted universe levels)

open Equiv-Reasoning

--  _equiv⟨_⟩_ : ∀ (x : A) (y z : A) -> Equiv x y  -> Equiv y z  -- h2
-- transitivity proof using chains of equations
trans' : ∀ {A : Set} (x y z : A)
    -> Equiv x y 
    -> Equiv y z 
    -------------
    -> Equiv x z 
trans' x' y' z' h1 h2 = 
    (_equiv⟨_⟩_ x' y' z' h1) 
        (_equiv⟨_⟩_ y' z' z' h2 (_∎ z') )  
-- kind of circuitous way, as we could've just used h2 directly.. as in:
--  .. = (_equiv⟨_⟩_ x' y' z' h1 h2) 
-- though perhaps not in 'chain of equation' form. So instead
-- the proof of Equiv y z (instead of using h2 directly) is constructed
-- out of applications of _equiv⟨_⟩_

-- reproducing basic nat datatype for convenience
-- (not using import here to avoid uses cyliclic uses prelude/equality <-> nat)
data ℕ : Set where
  zero : ℕ
  suc  : ℕ -> ℕ

_+_ : ℕ -> ℕ -> ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

postulate
  +-identity : ∀ (m : ℕ) -> (Equiv (m + zero) m)
  +-suc : ∀ (m n : ℕ) -> Equiv (m + suc n) (m + n)

-- A 'postulate' specifies a signature for an identifier 
-- but no definition. Here we postulate something proved earlier 
-- to save space

--  _equiv⟨_⟩_ : ∀ (x : A) (y z : A) -> Equiv x y  -> Equiv y z  
--  _equiv⟨⟩_ : ∀ (x : A) (y : A) -> Equiv x y -> Equiv x y
+-comm : ∀ (m n : ℕ) → Equiv (m + n) (n + m)
+-comm m zero = ({!  !} ) 
-- _equiv⟨_⟩_ m zero m : Equiv m zero → Equiv zero m → Equiv m m

-- _equiv⟨_⟩_ m zero m 
-- goal: Equiv (m + zero) (zero + m)
+-comm m (suc n) = {!   !} 

-- +-identity : ∀ (m : ℕ) → (Equiv (m + zero) m) ≡ m
-- +-suc      : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
