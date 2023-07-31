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
++-identity-l xs =  -- [] ++ x :: xs ≡ x :: xs
  begin 
    [] ++ xs
  ≡⟨⟩
    xs
  ∎ 

-- concatenation identity right
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
length-++ {A} (x :: xs) ys = 
  -- ?0 : length ((x :: xs) ++ ys) ≡ length (x :: xs) + length ys
  begin 
    length ((x :: xs) ++ ys)
  ≡⟨⟩
    length (x :: (xs ++ ys))
  ≡⟨ cong suc (length-++ xs ys ) ⟩ -- apply inductive hypothesis to xs and ys: 
                                   -- (length-++ xs ys), tack suc onto each side of congruence eq (≡)
    suc (length xs + length ys) 
    {- _+_ : ℕ → ℕ → ℕ
      zero + n = n
      (suc m) + n = suc (m + n) -}
  ≡⟨⟩ 
    (suc (length xs)) + length ys
  ∎

-- reversal

-- "using append, it is easy to formulate a function to reverse a list:"

reverse : ∀ {A : Set} -> List A -> List A 
reverse []        = [] 
reverse (x :: xs) = (reverse xs) ++ [ x ]

_ : reverse [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin 
    reverse (0 :: 1 :: 2 :: [])
  ≡⟨⟩
    reverse (1 :: 2 :: []) ++ [ 0 ]
  ≡⟨⟩
    (reverse (2 :: []) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    ((reverse ([]) ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    ([ 2 ] ++ [ 1 ]) ++ [ 0 ]
  ∎
-- ∀ s, t : SStr, rev(s ++ t) ≡ rev(t) ++ rev(s)
-- "show that the reverse of one list appended to another is the reverse of the second 
--  appended to the reverse of the first:"
reverse-++-distrib : ∀ {A : Set} -> ∀ (xs ys : List A) 
  -> reverse (xs ++ ys) ≡ (reverse ys) ++ (reverse xs)
reverse-++-distrib {A} [] ys = --  reverse ([] ++ ys) ≡ reverse ys ++ reverse []
  begin 
    reverse ([] ++ ys)
  ≡⟨⟩
    (reverse []) ++ (reverse ys)
  ≡⟨⟩
    [] ++ (reverse ys)
  ≡⟨⟩
    (reverse ys)
  ≡⟨ sym (++-identity-r (reverse ys)) ⟩ -- sym necessary to flip  [] ++ (reverse ys) ≡ (reverse ys) 
                                        -- to: (reverse ys) ≡ [] ++ (reverse ys)
    (reverse ys) ++ []
  ∎
reverse-++-distrib {A} (x :: xs) ys = 
  -- ?0 : reverse ((x :: xs) ++ ys) ≡ reverse ys ++ reverse (x :: xs)
  begin 
    reverse ((x :: xs) ++ ys) 
  ≡⟨⟩
    reverse (x :: (xs ++ ys)) -- (x :: xs) = (reverse xs) ++ [ x ]
  ≡⟨⟩
    reverse (xs ++ ys) ++ [ x ]
   -- ?1 : reverse (xs ++ ys) ++ [ x ] ≡ reverse ys ++ reverse (x :: xs)
  ≡⟨ cong ( _++ [ x ]) (reverse-++-distrib xs ys) ⟩ -- ?1 : reverse (xs ++ ys) ++ [ x ] ≡ reverse ys ++ reverse (x :: xs)
    (reverse ys ++ reverse xs) ++ [ x ] 
  ≡⟨⟩ 
    (reverse ys ++ reverse xs) ++ [ x ] 
  ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
    reverse ys ++ (reverse xs ++ [ x ]) 
  ≡⟨⟩ -- recall ind. case of defining eq for reverse(_) op:
      --    reverse (x :: xs) = (reverse xs) ++ [ x ]
      -- .. so the above automatically gets rewritten to:
    reverse ys ++ (reverse (x :: xs))
      -- which matches exactly the shape of the goal 
  ∎
{- _++_ : ∀ {A : Set} -> List A -> List A -> List A 
  [] ++ ys        = ys 
  (x :: xs) ++ ys = x :: ( xs ++ ys )
-}

-- reverse involutive

-- "a function is an involution if when applied twice it acts as the identity
--  function. Show that reverse is an involution:"

reverse-involutive : ∀ {A : Set} -> ∀ (alist : List A) 
  -> reverse (reverse alist) ≡ alist

-- ?0 : reverse (reverse []) ≡ []
reverse-involutive {A} [] = 
  begin 
    reverse (reverse [])
  ≡⟨⟩
    reverse ([])
  ≡⟨⟩
    []
  ∎
-- ?1 : reverse (reverse (x :: xs)) ≡ x :: xs
reverse-involutive {A} (x :: xs) = 
  begin 
    reverse (reverse (x :: xs))
  ≡⟨⟩
    reverse ((reverse xs) ++ [ x ] )
  ≡⟨ reverse-++-distrib {A} (reverse xs) [ x ] ⟩
    (reverse [ x ]) ++ (reverse (reverse xs))
  ≡⟨⟩ -- reverse (reverse xs ++ [ x ])
    ((reverse []) ++ [ x ]) ++ (reverse (reverse xs))
  ≡⟨⟩
    ([] ++ [ x ]) ++ (reverse (reverse xs))
  ≡⟨⟩
    [ x ] ++ (reverse (reverse xs))
  ≡⟨ cong (x ::_) (reverse-involutive {A} xs) ⟩ 
    --  x :: reverse (reverse xs) ≡ x :: xs
    -- (reverse-involutive {A} xs) gives: reverse (reverse xs) ≡ xs
    -- so: cong (x ::_) (reverse-involutive {A} xs) ⟩ tacks an [ x ] on the lhs and rhs
    -- of the above ≡
    x :: xs
  ≡⟨⟩ -- definitionally eq to:
    [ x ] ++ xs
  ∎ 
  -- reverse-++-distrib {A} (reverse xs) [ x ]