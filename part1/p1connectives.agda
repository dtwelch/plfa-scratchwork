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
        
        -- goal: 
        -- record { 
        --      to = proj₁ ⟨ to p , from p ⟩ ;  from = proj₂ ⟨ to p , from p ⟩ 
        -- } ≡ p
        from∘to = λ (p : A iff B) -> ( {!   !} ) 
    }