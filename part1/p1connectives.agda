module p1connectives where 

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)

open import Function using (_∘_)
open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality; _⇔_)
open plfa.part1.Isomorphism.≃-Reasoning

-- given two propositions A and B, the conjunction A × B holds if both A and B hold. We formalize
-- this idea by declaring a suitable datatype:

infixr 2 _×_  -- so m ≤ n × n ≤ p parses as (m ≤ n) × (n ≤ p)
data _×_ (A B : Set) : Set where 
    ⟨_,_⟩ : 
           A
        -> B
        --------
        -> A × B 

-- evidence that A × B holds is of the form ⟨ M , N ⟩ 
-- where M provides evidence that A and N provides evidence that B holds 

proj₁ : ∀ {A B : Set} 
    -> A × B 
    --------
    -> A
proj₁ {A} {B} (⟨_,_⟩ x y) = x
-- nicer way of writing (that uses the mixfix below):
-- proj₁ {A} {B} ⟨ x , y ⟩  = x
-- the {A} and {B} bit there can also be removed 
-- (necessary only if you want to explicitly annotate 
--  types in various spots in the defining equations)
-- (ignore pattern _ also used):
---- proj₁ ⟨ x , _ ⟩  = x

proj₂ : ∀ {A B : Set} 
    -> A × B 
    --------
    -> B 
proj₂ {A} {B} (⟨_,_⟩ x y) = y

-- when ⟨_,_⟩ appears on the left hand side of a defining equation, 
--      it's a destructing an entity being matched o
 
-- when ⟨_,_⟩ appears on the right hand side of of a defining equation,
--      it's a constructor for the (product) datatype _×_

-- projection fns provide identity over products
η-× : ∀ {A B : Set} (w : A × B) -> ⟨ proj₁ w , proj₂ w ⟩ ≡ w 
η-× {A} {B} (⟨_,_⟩ x y) = refl
-- goal is: ⟨ proj₁ ⟨ x , y ⟩ , proj₂ ⟨ x , y ⟩ ⟩ ≡ ⟨ x , y ⟩
-- which is definitionally equal (via the way the prod fns are defined) to:
-- ⟨ x , y ⟩ ≡ ⟨ x , y ⟩
--
-- which is dischargeable via refl

-- alternative way of modeling products using records 
-- (provides some shortcuts vs data version... η-equality
--  and other properties somewhat less verbose)
record _×'_ (A B : Set) : Set where 
    constructor ⟨_,_⟩'
    field
        proj₁' : A 
        proj₂' : B 

-- record { proj₁′ = M ; proj₂′ = N } corresponds to term: ⟨ M , N ⟩ ..
-- the constructor part allows us to construct 'instances' instead of having
-- to write, as we would usually: record { proj₁′ = M ; proj₂′ = N } 

--  cartesian products in set theory correspond to record types in computing

-- products are commutative and associative up to isomorphism

-- for commutativity, the to fn swaps a pair, taking ⟨ x , y ⟩ to ⟨ y , x ⟩ 
-- and the from fn does the same (up to renaming)

×-comm : ∀ {A B : Set} -> A × B ≃ B × A 
×-comm {A} {B} = 
    -- construct a record since top level app is ≃ 
    -- (and ≃ is modeled using a record)
    record { 
        -- NOTE: the reason to can use A × B as the type for p in the λ below is due to 
        -- the way the record for _≃_ is defined: A is the lhs, B is the rhs.
        -- (see p1isomorphism _≃_)
        to      =  λ (p : A × B) -> ⟨ (proj₂ p) , (proj₁ p) ⟩  ;
        -- can also do it like (via pattern matching lambdas):
        -- λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
        from    = λ (p : B × A) -> ⟨ (proj₂ p) , (proj₁ p) ⟩  ;

        -- goal: ⟨ proj₂ ⟨ proj₂ p , proj₁ p ⟩ , proj₁ ⟨ proj₂ p , proj₁ p ⟩ ⟩ ≡ p

        to∘from = λ (p : B × A) -> (η-× p)    ; -- here's the type of (η-× p): ⟨ proj₁ p , proj₂ p ⟩ ≡ p
        -- which is definitionally equal to (after applying/'eliminating' the projection fns):
        --  Ev: ⟨ p , p ⟩ ≡ p 
        --
        -- NOW here's the goal we need to EV to match...:
        --  ⟨ proj₂ ⟨ proj₂ p , proj₁ p ⟩ , proj₁ ⟨ proj₂ p , proj₁ p ⟩ ⟩ ≡ p
        -- which is definitionally equal to:
        --  ⟨ proj₂ ⟨ p , p ⟩ , proj₁ ⟨ p , p ⟩ ⟩ ≡ p
        -- which is definitionally equal to:
        --  ⟨ p , p ⟩ ≡ p
        -- so EV and ⟨ p , p ⟩ ≡ p match and can be discharged via refl

        from∘to = λ (p : A × B) -> (η-× p) 
    }

-- messing around:
rev : ∀ {A B} 
    -> A × B 
    --------
    -> B × A 
rev {A} {B} (⟨_,_⟩ x y) = ⟨ y , x ⟩

 -- associativity

-- NOTE: will probably need to just do pattern matching here, 
-- it's more manageable when dealing w/ proofs involving records it seems

×-assoc : ∀ {A B C : Set} -> (A × B) × C ≃ A × (B × C) 
-- an attempt to do with w/o pattern matching.. got stuck on to∘from, from∘to
×-assoc {A} {B} {C} = 
    record {
        --                                    -------A---------  -------------(B × C)---------------           
        to         =  λ (p : (A × B) × C) -> ⟨ (proj₁ (proj₁ p)) , ⟨ (proj₂ (proj₁ p)) , (proj₂ p) ⟩ ⟩ ;

                --                            ------------(A × B)----------    -------C-------         
        from       =  λ (p : A × (B × C)) -> ⟨ ⟨ proj₁ p , proj₁ (proj₂ p) ⟩ , proj₂ (proj₂ p) ⟩ ;
        -- pattern matching lambdas below...
        to∘from     = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ -> refl } ; 
        from∘to     = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ -> refl }
    }

-- exercise iff≃× (iff and some lemmas reproduced here from last ch):

-- equivalence of propositions (if and only if)
record _iff_ (A B : Set) : Set where 
    field 
        to      : A -> B 
        from    : B -> A
    
open _iff_

-- show that equivalence is reflexive, symmetric, and transitive 

-- reflexivity
_iff_-refl : {A : Set} 
    ----------
    -> A iff A 
_iff_-refl {A} = 
    record {
        to   = λ (x : A) -> x ;
        from = λ (x : A) -> x
    }

-- symmetry
_iff_-sym : ∀ {A B : Set} 
    -> A iff B 
    ----------
    -> B iff A
_iff_-sym {A} {B} iffAB =  
    record {
        to      = λ (x : B) -> (from iffAB x) ;
        from    = λ (x : A) -> (to iffAB x)
        
    }

-- transitivity
_iff_-trans : {A B C : Set} 
    -> A iff B 
    -> B iff C 
    ----------
    -> A iff C 
_iff_-trans {A} {B} {C} iffAB iffBC =
    record {
        to      = λ (x : A) -> to iffBC (to iffAB x) ;
        from    = λ (x : C) -> from iffAB (from iffBC x)
    }
-------------------------

iff≃× : ∀ {A B : Set} -> (A iff B) ≃ (A -> B) × (B -> A) 
iff≃× {A} {B} = 
    record {
        -- given a proposition p, construct a term that matches the goal:
        -- the to and from in the λ body below are the fns defined in the 
        -- record for _iff_
        to      = λ (p : A iff B) -> ⟨ (to p) , (from p) ⟩  ; -- goal: (A -> B) × (B -> A) 

        -- given a product of the form (A -> B) × (B -> A) show that A iff B 
        -- holds by constructing a term with that as its type
        from    = λ (p : (A -> B) × (B -> A)) ->  -- goal: A iff B
            record {
                to   = (proj₁ p) ; -- goal: A -> B   (proj₁ p) : A -> B
                from = (proj₂ p)   -- goal: B -> A   (proj₂ p) : B -> A  
                -- (the record {..} 'constructs' a bi-implication of the 
                --  shape we want using the product p we know)
            } ; 
        to∘from = λ (p : (A -> B) × (B -> A)) -> (η-× p) ; -- goal : ⟨ proj₁ p , proj₂ p ⟩ ≡ p (use product identity fn η-× over given p)
        
        -- iff≃×  ∀ {A B  Set} -> (A iff B) ≃ (A -> B) × (B -> A) 

        -- goal: 
        -- record { 
        --      to = proj₁ ⟨ to p , from p ⟩ ;  from = proj₂ ⟨ to p , from p ⟩ 
        -- } ≡ p
        -- (the record in the goal comment above can be made definitionally equal to p,
        --  so refl which gives us φ ≡ φ)
        from∘to = λ (p : A iff B) -> refl 
    }

-- truth 

data ⊤ : Set where 

    tt : 
        --
        ⊤

-- evidence that ⊤ holds is of the form tt.

-- nullary case of η-× is η-⊤, which asserts that any value of 
-- type ⊤ must be equal to tt

-- ⊤ is unit
η-⊤ : ∀ (w : ⊤) -> tt ≡ w 
η-⊤ tt = refl -- matching on tt leaves us to show tt ≡ tt, (refl from there) 
-- e.g., η-⊤ b = refl wouldn't work we need to instantiate w on the right hand side of ≡ 
-- to tt (since the left is 'hardwired' to tt specifically in the pattern) in ∀ (w : T) -> tt ≡ w


-- NOTE: doing it with pattern matching λs allows two proofs by refl (definitional equality works 
-- w/o needing any helper lemmas.. the version below is a mostly completed explicit non pattern matching
-- version that uses projection functions -- but requires a helper lemma (I think) for the from∘to case
{-
⊤-identity-l : ∀ {A : Set} -> ⊤ × A ≃ A 
⊤-identity-l {A} = record {
        to      = λ (y : (⊤ × A)) -> (proj₂ y) ;
        from    = λ (y : A) -> ⟨ tt , y ⟩ ;

        to∘from = λ (y : A) -> refl ; -- need a term proj­₂ ⟨ tt , y ⟩ ≡ y ... 
        -- the lhs (proj₂ ⟨ tt , y ⟩) is definitionally equal to y, so we get y ≡ y 
        -- after simplification.. which holds via refl

        from∘to = λ (y : (⊤ × A)) -> {!   !}
        -- from∘to =  λ{ ⟨ tt , ⟨ _ , x ⟩ ⟩ -> x  }
    }

-- ⊤-id-helper : ∀ {A : Set} -> ⊤ × A -> ...

-}

-- unit is left identity of × up to isomorphism
⊤-identity-l : ∀ {A : Set} -> ⊤ × A ≃ A 
⊤-identity-l {A} = record {
        to      = λ{ ⟨ tt , y ⟩  -> y } ;
        from    = λ{ y -> ⟨ tt , y ⟩ } ;
        to∘from = λ{ y -> refl } ; 

        -- sample goal for from∘to:
        -- ?0 : (x : ⊤ × A) →
        --      (λ { y → ⟨ tt , y ⟩ }) ((λ { ⟨ tt , y ⟩ → y }) x) ≡ x
        -- the big cluster of nested lambas on lhs of ≡ is definitionally equal to x 
        -- (the product-typed argument being applied to the outermost λ term). So the 
        -- goal becomes x ≡ x which is proved via refl
        from∘to = λ{ ⟨ tt , y ⟩ -> refl  }
    } 

-- unit is right identity for × upto isomorphism
⊤-identity-r : ∀ {A : Set} -> (A × ⊤) ≃ A 
⊤-identity-r {A} = 
    ≃-begin
        (A × ⊤)
    ≃⟨ ×-comm ⟩
        (⊤ × A) 
    ≃⟨ ⊤-identity-l ⟩
        A
    ≃-∎
    
-- disjunction is sum

-- "Given two propositions A and B, the disjunction A ⊎ B holds if either A holds
--  or B holds. We formalise this idea by declaring a suitable inductive type:"

-- Q: why ⊎ for the symbol and not ⋎ or something? (⊎ seems like multiset notation..)
data _⊎_ (A B : Set) : Set where 

    inj₁ : 
        A 
        --------
        -> A ⊎ B 

    inj₂ : 
        B 
        --------
        -> A ⊎ B 

case-⊎ : ∀ {A B C : Set} 
    -> (A -> C)     -- f
    -> (B -> C)     -- g
    -> A ⊎ B        -- h1
    -----------
    -> C          --  inj₁ h1 produces a type A ⊎ B from the pattern variable h1 : A
case-⊎ {A} {B} {C} f g (inj₁ h1) = f h1 
case-⊎ {A} {B} {C} f g (inj₂ h1) = g h1 

-- " .. matching against inj₁ and inj₂ is typical of how we exploit evidence that a 
--  disjunction like A ⊎ B holds."

-- "When inj₁ and inj₂ appear on the right-hand side of an equation we refer to them 
--  as constructors, and when they appear on the left-hand side we refer to them as destructors."

-- "Applying the destructor to each of the constructors is the identity:"
η-⊎ : ∀ {A B : Set} (w : A ⊎ B) -> case-⊎ inj₁ inj₂ w ≡ w 
η-⊎ {A} {B} (inj₁ x) = refl  -- case-⊎ inj₁ inj₂ (inj₁ x) ≡ inj₁ x
η-⊎ {A} {B} (inj₂ x) = refl  -- case-⊎ inj₁ inj₂ (inj₁ x) ≡ inj₁ x

-- so inj₁ and inj₂ are destructors if on the lhs of a definition eq, 
-- on the rhs, they are constructors for A ⊎ B

-- more generally, we can also throw in an arbitrary function from a disjunction:
uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B -> C) (w : A ⊎ B) ->
    case-⊎ ( h ∘ inj₁) (h ∘ inj₂) w ≡ h w
-- inj₁ : A -> A ⊎ B
-- inj₂ : B -> A ⊎ B
-- h ∘ inj₁ : (x : A) -> C
-- h ∘ inj₂ : (x : B) -> C
uniq-⊎ {A} {B} {C} h (inj₁ x) = refl
uniq-⊎ {A} {B} {C} h (inj₂ x) = refl

infixr 1 _⊎_ 

-- so A × C ⊎ B × C parses as (A × C) ⊎ (B × C)

-- some clarification on choice of symbol (⊎):

-- "In set theory, it is also sometimes called the disjoint union, 
--  and in computing it corresponds to a variant record type. 
--  Among other reasons for calling it the sum, note that if type A 
--  has m distinct members, and type B has n distinct members, 
--  then the type A ⊎ B has m + n distinct members"

-------- exercises:

-- to allow the system to ensure that pattern matching is complete
-- can't do the thing from the last chapter in each to = λ { (inj x) -> } 
-- agda (rightly I guess) isn't convinced that it will match all cases?
helper-comm : ∀ {A B : Set} -> A ⊎ B -> B ⊎ A 
helper-comm (inj₁ a) = (inj₂ a) 
helper-comm (inj₂ b) = (inj₁ b)

helper-elim : ∀ {A B : Set} -> (w : A ⊎ B) -> 
    helper-comm (helper-comm w) ≡ w 
helper-elim {A} {B} (inj₁ a) = refl 
helper-elim {A} {B} (inj₂ b) = refl

-- sum is commutative up to isomorphism (_≃_)
⊎-comm : ∀ {A B : Set} -> A ⊎ B ≃ B ⊎ A 
⊎-comm {A} {B} = 
    record {
        to      = λ (y : A ⊎ B) -> helper-comm {A} {B} y  ;
        from    = λ (y : B ⊎ A) -> helper-comm {B} {A} y ;

        -- helper-comm (helper-comm y) ≡ y
        -- has to be {B} {A} in the app since y : B ⊎ A
        to∘from = λ (y : B ⊎ A) -> (helper-elim {B} {A} y) ; 
        from∘to = λ (y : A ⊎ B) -> (helper-elim {A} {B} y) 
    }

{-
inj₁ : 
        A 
        --------
        -> A ⊎ B 

    inj₂ : 
        B 
        --------
        -> A ⊎ B
-}

-- inj₂ {A ⊎ B} {C} (inj₁ {A} {B} x)
⊎-assoc-helper-r : ∀ {A B C : Set} -> A ⊎ (B ⊎ C) -> (A ⊎ B) ⊎ C
⊎-assoc-helper-r {A} {B} {C} (inj₁ x)           = (inj₁ {A ⊎ B} {C} (inj₁ {A} {B} x))   -- matching A
⊎-assoc-helper-r {A} {B} {C}    (inj₂ (inj₁ x)) = inj₁ {A ⊎ B} {C} (inj₂ {A} {B} x)     -- matching B
⊎-assoc-helper-r {A} {B} {C}    (inj₂ (inj₂ x)) = (inj₂ {A ⊎ B} {C} x)                  -- matching C


⊎-assoc-helper-l : ∀ {A B C : Set} -> (A ⊎ B) ⊎ C -> A ⊎ (B ⊎ C)
⊎-assoc-helper-l {A} {B} {C}    (inj₁ (inj₁ x))  = inj₁ {A} {B ⊎ C} x                   -- matching A
⊎-assoc-helper-l {A} {B} {C}    (inj₁ (inj₂ x))  = inj₂ {A} {B ⊎ C} (inj₁ {B} {C} x)    -- matching B
⊎-assoc-helper-l {A} {B} {C} (inj₂ x)            = inj₂ {A} (inj₂ {B} {C} x)            -- matching C

-- explicit instantiations used on some of the patterns above..

-- inj₂ {A ⊎ B}{C} (inj₁ {A} {B} x) -- gives: (A ⊎ B) ⊎ C


-- inj₁ {A}{B ⊎ C} (inj₁ {A} {B ⊎ C} x) -- gives: (A ⊎ B) ⊎ C



-- notes on pattern matching in the above helper method: ---

-- pattern (inj₁ (inj₁ x))      --> x : A 
-- pattern (inj₁ (inj₂ x))      --> x : B
-- pattern (inj₂ x)             --> x : C

-- three patterns (as opposed to two) are necessary to further decompose 
-- the left subexpression of (A ⊎ B) ⊎ C . Specifically:

-- pattern (inj₁ x)             --> x : A ⊎ B (left subexpression)
-- pattern (inj₁ (inj₁ x))      --> x : A 
-- pattern (inj₁ (inj₂ x))      --> x : B

-- no need for two patterns to handle the right subexpression since 
-- it's just C:
-- pattern (inj₂ x)             --> x : C (right subexpression)
---------

⊎-l-cancel : ∀ {A B C : Set} -> (w : (A ⊎ B) ⊎ C) 
    -> ⊎-assoc-helper-r (⊎-assoc-helper-l w) ≡ w
⊎-l-cancel {A} {B} {C}    (inj₁ (inj₁ x))  = refl       -- matching A
⊎-l-cancel {A} {B} {C}    (inj₁ (inj₂ x))  = refl       -- matching B
⊎-l-cancel {A} {B} {C} (inj₂ x)            = refl       -- matching C

⊎-r-cancel : ∀ {A B C : Set} -> (w : A ⊎ (B ⊎ C))
    -> ⊎-assoc-helper-l (⊎-assoc-helper-r w) ≡ w
⊎-r-cancel {A} {B} {C} (inj₁ x)           = refl   
⊎-r-cancel {A} {B} {C}    (inj₂ (inj₁ x)) = refl     -- matching B
⊎-r-cancel {A} {B} {C}    (inj₂ (inj₂ x)) = refl     -- matching C


-- sum is associative up to isomorphism (_≃_)
⊎-assoc : ∀ {A B C : Set} -> (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc {A} {B} {C} = 
    record {
        to      = λ (x : (A ⊎ B) ⊎ C) -> (⊎-assoc-helper-l x) ;
        from    = λ (x : A ⊎ (B ⊎ C)) -> (⊎-assoc-helper-r x) ;

        to∘from = λ (x : A ⊎ (B ⊎ C)) -> (⊎-r-cancel x) ; 
        from∘to = λ (x : (A ⊎ B) ⊎ C) -> (⊎-l-cancel x) 
    }

-- false ⊥ never holds 

data ⊥ : Set where 
    -- no clauses!

⊥-elim : ∀ {A : Set} 
    -> ⊥
    ----
    -> A 
⊥-elim () 
-- given evidence that ⊥ holds, we can conclude anything

uniq-⊥ : ∀ {C : Set} (h : ⊥ -> C) (w : ⊥) -> ⊥-elim w ≡ h w 
uniq-⊥ {C} h () 

⊥-count : ⊥ -> ℕ
⊥-count ()

-- in example above, absurd patter '()' indicates 
-- that no value can match type ⊥

-- ⊥ elimination
⊥-el : ∀ {A : Set} -> ⊥ ⊎ A -> A
⊥-el {A} (inj₂ x) = x 

-- ⊥ introduction
⊥-in : ∀ {A : Set} -> A -> ⊥ ⊎ A
⊥-in {A} x = (inj₂ {⊥} {A} x)

intro-elim-⊥ : ∀ {A : Set} -> (w : A) ->
    ⊥-el (⊥-in w) ≡ w 
intro-elim-⊥ {A} w = refl 

elim-intro-⊥ : ∀ {A : Set} -> (w : ⊥ ⊎ A) ->
    ⊥-in (⊥-el w) ≡ w 
elim-intro-⊥ {A} (inj₂ x) = refl 

-- ⊥ is left identity of sums (⊎) up to isomorphism (≃)
⊥-id-l : ∀ {A : Set} -> ⊥ ⊎ A ≃ A 
⊥-id-l {A} = 
    record {
        to      = λ (x : ⊥ ⊎ A) -> (⊥-el x) ;
        from    = λ (x : A)     -> (⊥-in x) ;
        to∘from = λ (x : A)     -> (intro-elim-⊥ x) ;
        from∘to = λ (x : ⊥ ⊎ A) -> (elim-intro-⊥ x) 
    }

⊥-el2 : ∀ {A : Set} -> A ⊎ ⊥ -> A
⊥-el2 {A} (inj₁ x) = x 

⊥-in2 : ∀ {A : Set} -> A -> A ⊎ ⊥
⊥-in2 {A} x = inj₁ {A} {⊥} x

⊥-to∘from : ∀ {A : Set} -> (w : A) ->
    ⊥-el2 (⊥-in2 w) ≡ w 
⊥-to∘from {A} x = refl

⊥-from∘to : ∀ {A : Set} -> (w : A ⊎ ⊥) ->
    ⊥-in2 (⊥-el2 w) ≡ w 
⊥-from∘to {A} (inj₁ x) = refl 

-- ⊥ is right identity of sums (⊎) up to isomorphism (≃)
⊥-id-r : ∀ {A : Set} -> A ⊎ ⊥ ≃ A 
⊥-id-r {A} =
    record {
        to      = λ (x : A ⊎ ⊥) -> (⊥-el2 x) ;
        from    = λ (x : A)     -> (⊥-in2 x)  ;
        to∘from = λ (x : A)     -> (⊥-to∘from x)  ;
        -- (elim-intro-⊥ (helper-comm x)) : ⊥-in (⊥-el (helper-comm x)) ≡ helper-comm x
        from∘to = λ (x : A ⊎ ⊥) -> (⊥-from∘to x)
    }
{-
-- this approach tries to be a bit clever w/ commutativity of sum (⊎)
-- but got bogged down in the from∘to part (if figured out, would allow deletion
-- of lemmas: ⊥-to∘from , ⊥-in2, ⊥-el2 , ⊥-from∘to)
    record {
        to      = λ (x : A ⊎ ⊥) -> ⊥-el (helper-comm {A} {⊥} x) ;
        from    = λ (x : A)     -> helper-comm {⊥} {A} (⊥-in x)  ;
        to∘from = λ (x : A)     -> refl ;
        -- (elim-intro-⊥ (helper-comm x)) : ⊥-in (⊥-el (helper-comm x)) ≡ helper-comm x
        from∘to = λ (x : A ⊎ ⊥) -> {!   !} 
    }
-}

-- elimination of a function
η--> : ∀ {A B : Set} (f : A -> B) -> ( λ (x : A) -> f x ) ≡ f
η--> {A} {B} f = refl

currying : ∀ {A B C : Set} -> (A -> B -> C) ≃ (A × B -> C) 
currying {A} {B} {C} = 
    record {
        -- A -> (B -> C) -> (A × B) -> C
        -- version of to w/o pattern matching (uses the record proj functions instead)
        -- to      = λ (f: (A -> (B -> C)) -> λ (dom : A × B) -> f (proj₁ dom) (proj₂ dom) 
        to      = λ (f : (A -> (B -> C))) -> λ { ⟨ x , y ⟩ -> f x y } ;
        from    = λ (f : (A × B) -> C)    -> λ (x : A) -> λ (y : B) -> f ⟨ x , y ⟩    ;

        -- ?1: (y: A × B → C) -> (λ { ⟨ x , y ⟩  y₁ ⟨ x , y ⟩ }) ≡ y
        to∘from = λ (f : (A × B) -> C) -> extensionality λ{ ⟨ x , y ⟩ -> refl }    ; -- η-→ {A × B} {C} f   ;
        from∘to = λ (f : (A -> (B -> C))) -> refl  
    }

    -- ?0 : (λ { ⟨ x , y ⟩ → f ⟨ x , y ⟩ }) ≡ f

    --
    -- ?1 : (λ x y → (λ { ⟨ x , y ⟩ → f x y }) ⟨ x , y ⟩) ≡ f
    -- discarding the pattern deconstruction λ:
    --?1 : (λ (x : A) (y : B) → (λ (f : A × B) -> f (proj₁ f) (proj₂ f) ) (⟨_,_⟩ x y) ) ≡ f 

-- reproducing compose for ref. (from top of this module)
{-
_∘_ : ∀ {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)
g ∘ f  =  λ x -> g (f x)
-}

->-distrib-⊎ : ∀ {A B C : Set} -> (A ⊎ B -> C) ≃ ((A -> C) × (B -> C))
->-distrib-⊎ {A} {B} {C} = 
    record {
        -- (A ⊎ B → C) → (A → C) × (B → C)
        to      = λ (f : (A ⊎ B) -> C) -> ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ ;
        from    = {!   !} ;
        to∘from = {!   !} ;
        from∘to = {!   !} 
    }