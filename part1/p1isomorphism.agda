module p1isomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

-- composition
_∘_ : ∀ {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)
(g ∘ f) x  = g (f x)

-- can also do it this way:
_∘'_ : ∀ {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)
g ∘' f  =  λ x -> g (f x)

-- extensionality
postulate 
  extensionality : ∀ {A B : Set} (f g : A -> B)
    -> (∀ (x : A) -> f x ≡ g x)
    ----------------------------
    -> f ≡ g

-- ".. consider that we need results from two libraries, one where addition is 
--  defined, as in Chapter Naturals, and one where it is defined the other way 
--  around."
-- 
-- Note: normal _+_ operator defines the patterns different (case patterns flipped):
-- _+_ : ℕ → ℕ → ℕ
-- zero + n = n                -- base case
-- (suc m) + n = suc (m + n)   -- ind hypo

_+'_ : ℕ -> ℕ -> ℕ
m +' zero = m 
m +' (suc n) = suc (m +' n)

-- +-comm : ∀ (m n : ℕ) -> (m + n) ≡ (n + m)
-- +-suc  : ∀ (m n : ℕ) -> m + suc n ≡ suc (m + n)

-- helper fn:
helper : ∀ (m n : ℕ) -> m +' n ≡ n + m
helper m zero =  refl  -- m + zero or m +' zero both match the base case and simplification happens to get m ≡ m 
helper m (suc n) = cong suc (helper m n) 

-- we want a theorem to show that _+_ and _+'_ (defined above) always
-- give back the same result given the same arguments (see above para for proof via helper lemma idea)
same-app : ∀ (m n : ℕ) -> m +' n ≡ m + n
same-app m n rewrite +-comm m n = helper m n

-- some details on proof for 'helper' constant above: 

-- the right hand side (above) beginning with 'cong' constructs a term that has the following 
-- as its type^*:
--  (m +' suc n) ≡ suc n + m
-- so we need to construct a term of this general shape ^*OR one definitionally equal 
-- via ≡ (based on the way its constructor defined in the datatype). Start w/ ind. hypothesis
--   helper m n 
-- which produces a term of rougly the shape of the goal .. i.e.: an ≡-term w/ an app of _+'_ 
-- as the top level subterm of the lhs and an app of _+_ on the rhs. Here is the term
-- that results from the ind. hypothesis app (helper m n):
--   (m +' n) ≡ n + m
-- now it just needs to get 'turned/transformed' into the goal: (m +' suc n) ≡ suc n + m..
-- This is done via:
--   cong suc (helper m n)
-- cong applies the provided fn (in this case, suc(·)) to the evidence produced by 
-- the inductive hypothesis to produce a term seemingly different (but VERY) close to 
-- the goal: 
--   (m +' suc n) ≡ suc (n + m)    -- this is the goal type
--   suc (m +' n) ≡ suc (n + m)    -- this type results from: cong suc (helper m n)
-- these two terms actually match (see how _+'_ ind. case below):
--   x +' (suc y) = suc (x +' y)   -- ind. case of _+'_ .. (using x and y instead of m n)
-- ..
-- so the term that results from cong suc (helper m n) is definitionally equal to the goal.

same : _+'_ ≡ _+_
same = extensionality (_+'_) (_+_) 
    (λ x -> extensionality (_+'_ x) (_+_ x) ( λ y -> same-app x y ))
-- extensionality (λ m → extensionality {!(λ n → ?)!})
-- ?0 : (x : ℕ) → (m +' x) ≡ m + x
-- ------------
-- extensionality (λ x -> extensionality {!?!} )
-- ?0 : (x₁ : ℕ) → (x +' x₁) ≡ x + x₁  -- so it is a fn...

-- in the explicit version, you need to partially apply the outer λ to account for needing to 
-- apply functions f and g in a curried way this is why we do: extensionality (_+'_ x) (_+_ x) 
-- instead of just: extensionality (_+'_) (_+_) -- we already did that over the outermost extensionality
-- app 

-- isomorphism...
-- "two sets are isomorphic if they are in one-to-one correspondence. Here is a formal definition
--  of isomorphism:"
-- (symbol cmd is: \simeq
infix 0 _≃_ 

-- A 'isIsomorphicTo' B
record _≃_ (A B : Set) : Set where 
    field 
        to      : A -> B 
        from    : B -> A
        from∘to : ∀ (x : A) -> from (to x) ≡ x 
        to∘from : ∀ (y : B) -> to (from y) ≡ y

open _≃_

-- An isomorphism between sets A and B consists of four things:
-- 1. A function to from A to B,
-- 2. A function from from B back to A,
-- 3. Evidence from∘to asserting that from is a left-inverse for to,
-- 4. Evidence to∘from asserting that from is a right-inverse for to.

-- A record declaration behaves similar to a single-constructor data 
-- declaration (for example):
data _≃'_ (A B : Set): Set where
  mk-≃' : ∀ (to : A -> B) ->
          ∀ (from : B -> A) ->
          ∀ (from∘to : (∀ (x : A) → from (to x) ≡ x)) ->
          ∀ (to∘from : (∀ (y : B) → to (from y) ≡ y)) ->
          A ≃' B

long-to' : ∀ {A B : Set} -> (A ≃' B) -> (A -> B)
long-to' (mk-≃' f g g∘f f∘g) = f
-- to' (mk-≃' f _ _ _) = f    -- guess this approach would work too?

long-from' : ∀ {A B : Set} -> (A ≃' B) -> (B -> A)
long-from' (mk-≃' f g g∘f f∘g) = g
-- from' (mk-≃' _ g _ _) = g


-- isomorhism is reflexive - any set is isomorphic to itself

≃-refl : ∀ {A : Set} 
    --------
    -> A ≃ A 
≃-refl {A} = record 
    {
        to      = λ (v : A) -> v ;
        from    = λ (v : A) -> v ;
        from∘to = λ (v : A) -> refl ;
        to∘from = λ (v : A) -> refl 
    }

-- isomorphism is symmetric
≃-sym : ∀ {A B : Set} 
    -> A ≃ B 
    --------
    -> B ≃ A 
≃-sym {A} {B} isoH1 = record 
    {
        to   = from isoH1 ;  -- flip everything.. (from isoH1) extracts the 'from' component/fn of the isoH1 record
        from = to isoH1 ; -- ditto w/ to and even to∘from, from∘to
        from∘to = to∘from isoH1 ; 
        to∘from = from∘to isoH1
    }

{-
-- reproducing compose for ref. (from top of this module)

_∘_ : ∀ {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)
g ∘ f  =  λ x -> g (f x)
-}

-- isomorphism is transitive 
≃-trans : ∀ {A B C : Set} 
    -> A ≃ B 
    -> B ≃ C 
    --------
    -> A ≃ C 
--                  h1  h2
≃-trans {A} {B} {C} A≃B B≃C = record
    {
        -- need to construct a fn from A -> C using hypothesis (h1 and h2)
        to   = λ (v : A) -> ((to B≃C) ∘ (to A≃B)) v ;

        -- need to construct a term/fn from C -> A
        from = λ (v : C) -> ((from A≃B) ∘ (from B≃C)) v ;

        from∘to = λ (v : A) -> 
            begin  
                (from A≃B ∘ from B≃C) ((to B≃C ∘ to A≃B) v)
            ≡⟨⟩ -- removing the ∘ apps
                from A≃B ( from B≃C ( to B≃C ( (to A≃B) v) ) )
            ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B v)) ⟩
                from A≃B (to A≃B v)
            ≡⟨ from∘to A≃B v ⟩
                v
            ∎
        ;
        
        to∘from = λ (v : C) ->
            begin
                (to B≃C ∘ to A≃B) ((from A≃B ∘ from B≃C) v)
            ≡⟨⟩
                to B≃C (to A≃B ( from A≃B ((from B≃C) v) )) 
            ≡⟨ cong (to B≃C) ( to∘from A≃B ((from B≃C) v) ) ⟩
                to B≃C (from B≃C v)
            ≡⟨  to∘from B≃C v  ⟩
                 v  
            ∎
    }

-- this is for the to∘from part
-- to∘from                      : (r : A ≃ B) (y : B) -> to r (from r y) ≡ y
-- to∘from A≃B                  : (y : B) -> to A≃B (from A≃B y) ≡ y
-- to∘from A≃B ((from B≃C) v)   : to A≃B (from A≃B ((from B≃C) v)) ≡ ((from B≃C) v)

-- cong (to B≃C) ( to∘from A≃B ((from B≃C) v) )

-- to B≃C (to A≃B (from A≃B (from B≃C v))) ≡ to B≃C (from B≃C v)


-- if t1 is the term: to A≃B (from A≃B ((from B≃C) v)) ≡ ((from B≃C) v)
-- (type of last line above) then you do:
--      cong (from A≃B) t1
-- you get:
-- 
-----------------------------


-- from∘to                  :   (r : A ≃ B) (x : A) -> from r (to r x) ≡ x
-- from∘to B≃C              :   (x : B) -> from B≃C (to B≃C x) ≡ x
--  (adding the app: ((to A≃B) v) produces type: B 
 
-- cong (from A≃B) (from∘to B≃C (to A≃B v)) produces:
--  from A≃B (from B≃C (to B≃C (to A≃B v))) ≡ from A≃B (to A≃B v)
-- gives us:
--  from A≃B (to A≃B v)

-- Equational reasoning for isomorphism

-- (doesn't appear to be used - at least in this ch/sect)
module ≃-Reasoning where 
    infix  1 ≃-begin_
    infixr 2 _≃⟨_⟩_
    infix  3 _≃-∎

    ≃-begin_ : ∀ {A B : Set} 
        -> A ≃ B 
        --------
        -> A ≃ B 
    ≃-begin_ {A} {B} A≃B = A≃B

    _≃⟨_⟩_ : ∀ (A : Set) {B C : Set}
        -> A ≃ B 
        -> B ≃ C 
        --------
        -> A ≃ C 
    _≃⟨_⟩_ A {B} {C} A≃B B≃C = ≃-trans A≃B B≃C 

    _≃-∎ : ∀ (A : Set)
        --------
        -> A ≃ A
    _≃-∎ A = ≃-refl
 
open ≃-Reasoning

-- ".. embedding is a weakening of isomorphism. While an
--  isomorphism shows that two types are in one-to-one 
--  correspondence, an embedding shows that the first type
--  is included in the second; or equivalently, that there is
--  a many-to-one correspondence between the second type and
--  the first"

-- formal def of embedding

infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A -> B
    from    : B -> A
    from∘to : ∀ (x : A) -> from (to x) ≡ x
open _≲_

-- embedding is reflexive and transitive, but not symmetric

≲-refl : ∀ {A : Set} -> A ≲ A 
≲-refl {A} = record {
        to      = λ (v : A) -> v ;
        from    = λ (v : A) -> v ;
        from∘to = λ (v : A) -> refl
    }

≲-trans : ∀ {A B C : Set} -> A ≲ B -> B ≲ C -> A ≲ C 
≲-trans {A} {B} {C} A≲B B≲C =
    record {
        -- A -> C
        to      = λ (x : A) -> to B≲C ((to A≲B) x) ;

        -- C -> A
        from    = λ (x : C) -> from A≲B ((from B≲C) x) ;
-- NOTE: type queries involving cong don't appear to be working from within equational proofs
-- for some reason..
-- cong (to  A≲B) 
-- ?0 : from A≲B (from B≲C (to B≲C (to A≲B x))) ≡ x
        from∘to = λ (x : A) ->
            begin
                from A≲B (from B≲C (to B≲C (to A≲B x)))
            ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B x)) ⟩
                from A≲B (to A≲B x)
            ≡⟨ from∘to A≲B x ⟩
                x 
            ∎
    }

-- weak antisymmetry of ≲ 
-- todo: return to this (one case is pretty intricate)
{-
≲-antisym : ∀ {A B : Set}
    -> (A≲B : A ≲ B)
    -> (B≲A : B ≲ A)
    -> (to A≲B ≡ from B≲A)
    -> (from A≲B ≡ to B≲A)
    ----------------------
    -> A ≃ B 
≲-antisym {A} {B} A≲B B≲A to≡from from≡to = 
    record {
        to      = λ (x : A) -> {!   !} ;
        from    = {!   !} ;
        from∘to = {!   !} ;
        to∘from = {!   !}
    }
-}

-- every isomorphism implies an embedding (practice)

≃-implies-≲ : ∀ {A B : Set}
    -> A ≃ B 
    --------
    -> A ≲ B 
≃-implies-≲ {A} {B} A≃B = 
    record {
        to      = λ (x : A) -> (to A≃B x)   ;     -- A -> B
        from    = λ (x : B) -> (from A≃B x) ;     -- B -> A

        -- goal (x :A) -> from A≃B (to A≃B x) ≡ x
        from∘to = λ (x : A) -> (from∘to A≃B x)
    }

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
  