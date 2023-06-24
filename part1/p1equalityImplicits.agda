module p1EqualityImplicits where

-- called _≡_ in the text (rightly so)
-- so this is a super explicit (indexed) version of the official _≡_
data Equiv {A : Set} : A -> A -> Set where 
    refl : ∀ {x : A} -> Equiv x x 

trans : ∀ {A : Set} (x y z : A)
    -> Equiv x y 
    -> Equiv y z 
    ------------
    -> Equiv x z 
trans x' y' z' refl refl = refl

-- constructing the operators used to do forward chain 
-- reasoning about the Equiv datatype
module Equiv-Reasoning {A : Set} where 
    infix  1 begin_ 
    infixr 2 _equiv⟨⟩_  _equiv⟨_⟩_
    infix  3 _∎

    begin_ : ∀ {x y : A}
        -> Equiv x y 
        ------------
        -> Equiv x y 
    begin_ h = h

    -- asserting two terms of type A are equal
    _equiv⟨⟩_ : ∀ (x : A) {y : A}
        -> Equiv x y 
        -------------
        -> Equiv x y
    _equiv⟨⟩_ x' h1 = h1

    -- justified equivalence
    _equiv⟨_⟩_ : ∀ (x : A) {y z : A}
        -> Equiv x y 
        -> Equiv y z 
        ------------
        -> Equiv x z 
    _equiv⟨_⟩_ x' {y'} {z'} h1 h2 = trans x' y' z' h1 h2
    -- just remember the x in the pattern could've been called anything
    -- and since {y z : A} are in curly braces, we can't add them to the 
    -- pattern as easily as we can x' (i.e.: we need to say: {y'} {z'})..
    -- I guess this says we're explicitly filling in implicit types
    
    _∎ : ∀ (x : A)
        ------------
        -> Equiv x x 
    _∎ x = refl

open Equiv-Reasoning

trans' : ∀ {A : Set} (x y z : A) 
    -> Equiv x y 
    -> Equiv y z 
    ------------
    -> Equiv x z 
trans' x' y' z' xEqy yEqz = 
    begin 
        x'
    equiv⟨ xEqy ⟩ 
        y'
    equiv⟨ yEqz ⟩ 
        z'
    ∎

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

-- again, 'postulate' in agda means 'axiom' (there is no explicit axiom keyword)
postulate
  +-identity : ∀ (m : ℕ) -> Equiv (m + zero) m
  +-suc : ∀ (m n : ℕ) -> Equiv (m + suc n) (suc (m + n))

