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

×-comm : {A B : Set} -> A × B ≃ B × A 
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
        to∘from = λ (p : B × A) -> {!   !}  ;
        from∘to = {!   !} 
    }

-- messing around:
rev : ∀ {A B} 
    -> A × B 
    --------
    -> B × A 
rev {A} {B} (⟨_,_⟩ x y) = ⟨ y , x ⟩

