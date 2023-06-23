module p1equality2 where

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

module Equiv-Reasoning {A : Set} where 
    infix  1 begin_ 
    infixr 2 _equiv⟨⟩_  -- _equiv⟨_⟩_
   -- infix  3 _∎

-- constructing the operators used to do forward chain 
-- reasoning about the Equiv datatype
    begin_ : ∀ {x y : A}
        -> Equiv x y 
        ------------
        -> Equiv x y 
    begin_ h = h

    -- asserting two are equal 
    -- (ver. where no justification evidence/term of type A 
    --  is needed: ⟨⟩)
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
    -- pattern as easily as we can intro x' (we need to say: {y'} {z'})
    -- to tell the elaborator(?) that we're explicitly filling in implicit 
    -- types
    
    _∎ : ∀ (x : A)
        ------------
        -> Equiv x x 
    _∎ x = refl