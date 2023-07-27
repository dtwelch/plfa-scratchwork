module p1lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.part1.Isomorphism using (_≃_; _⇔_)

-- lists are defined in agda as follows:

data List(A : Set) : Set where 
    []      : List A 
    _::_    : A -> List A -> List A 

infixr 5 _::_ 

-- if A is a set, then List A is a set. The next two lines tell us that [] 
-- (pronounced 'nil') is a list of type A (called the empty list), and that
-- _::_ (pronounced 'cons', short for 'constructor') takes a value of type A
-- and a value of type List A and returns a value of type List A.

_ : List ℕ 
_ = 0 :: 1 :: 2 :: []

-- since _::_ associates to the right, the term above parses as 0 ∷ (1 ∷ (2 ∷ []))

-- here is the 'indexed' version of the formal parameter based version of the List
-- datatype from above:
--
--  data List' : Set -> Set where 
--    []'   : ∀ {A : Set} -> List' A 
--    _::'_ : ∀ {A : Set} -> A -> List' A -> List' A
--
-- each constructor takes the (type) parameter A as an implicit argument. So if we 
-- had done instead:
--    []'   : ∀ (A : Set) -> List' A 
--    _::'_ : ∀ (A : Set) -> A -> List' A -> List' A
--
-- we would have to write lists like:
-- _∷_ ℕ 0 (_∷_ ℕ 1 (_∷_ ℕ 2 ([] ℕ)))
--
-- we can also (as usual) supply arguments to the implicit {..} version too:
-- _∷_ {ℕ} 0 (_∷_ {ℕ} 1 (_∷_ {ℕ} 2 ([] {ℕ})))

pattern [_] z = z :: []
pattern [_,_] y z = y :: z :: []
pattern [_,_,_] x y z = x :: y :: z :: []
pattern [_,_,_,_] w x y z = w :: x :: y :: z :: []
pattern [_,_,_,_,_] v w x y z = v :: w :: x :: y :: z :: []
pattern [_,_,_,_,_,_] u v w x y z = u :: v :: w :: x :: y :: z :: []

-- note: patterns above (e.g., [4, 3, 7]) can be used either in the pattern 
-- on the left hand side of a defining equation (or in a term on the rhs of 
-- the equation).

-- append

infixr 5 _++_ 

_++_ : ∀ {A : Set} -> List A -> List A -> List A 
[] ++ ys        = ys 
(x :: xs) ++ ys = x :: ( xs ++ ys )

_ : [ 0 , 1 , 2 ] ++ [ 3 , 4 ] ≡ [ 0 , 1 , 2 , 3 , 4 ]
_ = 
  begin
    0 :: 1 :: 2 :: [] ++ 3 :: 4 :: [] 
  ≡⟨⟩ 
    0 :: ( 1 :: 2 :: [] ++ 3 :: 4 :: [] )
  ≡⟨⟩
    0 :: 1 :: ( 2 :: [] ++ 3 :: 4 :: [] )
  ≡⟨⟩
    0 :: 1 :: 2 :: ( [] ++ 3 :: 4 :: [] )
  ≡⟨⟩
    0 :: 1 :: 2 :: 3 :: 4 :: []
  ∎

-- Appending two lists takes linear time O(n) where n is is the 
-- number of items in the first list, xs.

-- append is associative

++-assoc : ∀ {A : Set} -> ∀ (xs ys zs : List A) 
  -> (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = 
  begin
    ([] ++ ys) ++ zs 
  ≡⟨⟩ 
    ys ++ zs
  ≡⟨⟩ -- this is equal to the rhs of the ≡
    [] ++ (ys ++ zs)
  ≡⟨⟩ 
    (ys ++ zs)
  ∎
++-assoc (x :: xs) ys zs = 
--?0 : ((x :: xs) ++ ys) ++ zs ≡ (x :: xs) ++ ys ++ zs
  begin 
    ((x :: xs) ++ ys) ++ zs
  ≡⟨⟩ 
    x :: (xs ++ ys) ++ zs
  ≡⟨⟩ 
    x :: ((xs ++ ys) ++ zs) 
  ≡⟨ cong (x ::_) (++-assoc xs ys zs) ⟩
    x :: (xs ++ (ys ++ zs))
  ∎

++-identity-l : ∀ {A : Set} -> ∀ (xs : List A) -> [] ++ xs ≡ xs
++-identity-l xs = 
-- [] ++ x :: xs ≡ x :: xs
  begin 
    [] ++ xs
  ≡⟨⟩
    xs
  ∎

++-identity-r : ∀ {A : Set} -> ∀ (xs : List A) -> xs ++ [] ≡ xs
++-identity-r []      = 
  begin 
    [] ++ []
  ≡⟨⟩
    []
  ∎  
++-identity-r (x :: xs) =
  -- (x :: xs) ++ [] ≡ x :: xs <- goal
  begin 
    (x :: xs) ++ []
  ≡⟨⟩
    x :: (xs ++ [])
  ≡⟨ cong (x ::_) (++-identity-r xs) ⟩
    x :: xs 
  ∎  

-- length

length : ∀ {A : Set} -> List A -> ℕ 
length []     = zero
length (_ :: xs) = suc (length xs)

_ : length [ 0 , 1 , 2 ] ≡ 3 
_ = 
  begin 
    length (0 :: 1 :: 2 :: [])
  ≡⟨⟩
    suc (length (1 :: 2 :: []))
  ≡⟨⟩
    suc (suc (length ( 2 :: [])))
  ≡⟨⟩
    suc (suc (suc (length {ℕ} ( [] ) ) ) )
  ≡⟨⟩
    suc (suc (suc (0) ) )
  ∎

-- reasoning about length

length-++ : ∀ {A : Set} -> ∀ (xs ys : List A) 
  -> length (xs ++ ys) ≡ (length xs) + (length ys)
length-++ {A} [] ys =
  begin 
    length ([] ++ ys)
  ≡⟨⟩
    (length{A} []) + (length ys)
  ≡⟨⟩
    zero + (length ys)
  ≡⟨⟩
    length ys
  ∎
length-++ {A} (x :: xs) ys = {!   !}
  -- ?0 : length ((x :: xs) ++ ys) ≡ length (x :: xs) + length ys