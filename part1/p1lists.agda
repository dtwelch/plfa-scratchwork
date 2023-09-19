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
  ≡⟨ cong (x ::_) (reverse-involutive {A} xs) ⟩ -- rewrites immediate prior term via ind. hypothesis on xs 
                                                -- (tacks a [ x ] on front of each side of resulting ≡ )
    --  x :: reverse (reverse xs) ≡ x :: xs
    -- (reverse-involutive {A} xs) gives: reverse (reverse xs) ≡ xs
    -- so: cong (x ::_) (reverse-involutive {A} xs) ⟩ tacks an [ x ] onto 
    -- the front of the lhs and rhs of the above ≡ 
    x :: xs
  ≡⟨⟩ -- definitionally eq to:
    [ x ] ++ xs
  ∎ 

-- map 

-- "map applies a function to every element of a list to generate a corresponding list.
-- Map is an example of a higher order fn, one which takes a fn as an argument and 
-- returns a function as a result"

map : ∀ {A B : Set} -> (A -> B) -> List A -> List B 
map {A} {B} f [] = []{B} -- (this also works: [] )
map f (x :: xs)  = (f x) :: (map f xs)

_ : map (suc) [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =  -- ?0 : map suc [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
  begin
    map (suc) (0 :: 1 :: 2 :: [])
  ≡⟨⟩ 
    (suc 0) :: map suc (1 :: 2 :: [])
  ≡⟨⟩ 
    (suc 0) :: (suc 1) :: map suc (2 :: [])
  ≡⟨⟩ 
    (suc 0) :: (suc 1) :: (suc 2) :: map suc ([])
  ≡⟨⟩ 
    (suc 0) :: (suc 1) :: (suc 2) :: []
  ≡⟨⟩ 
    1 :: 2 :: 3 :: []  
  ≡⟨⟩ 
    [ 1 , 2 , 3 ]
  ∎

-- "map requires time linear in the length of the list"

-- map compose

-- "prove that the map of a composition is equal to the composition of two maps:"
-- composition
--_∘_ : ∀ {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)
-- (g ∘ f) x  = g (f x)

postulate 
  extensionality : ∀ {A B : Set} (f g : A -> B)
    -> (∀ (x : A) -> f x ≡ g x)
    ----------------------------
    -> f ≡ g

all-points-same-helper : ∀ {A B C : Set} 
  -> ∀ (list : List A) 
  -> ∀ (g : B -> C) -> ∀ (f : A -> B)
  -> map g (map f list) ≡ map (λ x -> g (f x)) list 
all-points-same-helper {A} {B} {C} [] g f = 
-- goal: map g (map f []) ≡ map (λ x → g (f x)) []
  begin 
    map g (map f [])
  ≡⟨⟩
    map (λ (x : B) -> g x) ([])
  ≡⟨⟩
    []
  ≡⟨⟩ -- the other side of the ≡ reduces to [] too:
    map (λ (x : A) -> g (f x)) []
  ≡⟨⟩
    []
  ∎
  --  nb: xs@ gives the entire pattern (x :: xs₁) the name/handle: xs
all-points-same-helper {A} {B} {C} xs@(x :: xs₁) g f =
  -- map g (map f (x :: xs₁)) ≡ map (λ x₁ → g (f x₁)) (x :: xs₁) 
  begin 
    map g (map f (x :: xs₁))
  ≡⟨⟩
    -- by second defining eq of 'map' defn
    map g ( (f x) :: (map f xs₁) )
  -- ?1 : map g (f x :: map f xs₁) ≡ map (λ x₁ → g (f x₁)) (x :: xs₁)
  ≡⟨⟩     -- another application of map's second eq
    (g (f x)) :: ( map (g) (map f xs₁) ) 
  -- ( (f x) :: (map f xs₁) ) : List B
  ≡⟨ cong ( g (f x) ::_ ) (all-points-same-helper xs₁ g f) ⟩ 
    g (f x) :: map (λ x₁ -> g (f x₁)) xs₁
  ∎

{- map : ∀ {A B : Set} -> (A -> B) -> List A -> List B 
    map {A} {B} f [] = []{B} -- (this also works: [] )
    map f (x :: xs)  = (f x) :: (map f xs)
-}

map-compose : {A B C : Set} -> ∀ (g : B -> C) -> ∀ (f : A -> B) 
  -> map (g ∘ f) ≡ (map g) ∘ (map f)
-- (g : B -> C) (f : A -> B) → map (g ∘ f) ≡ map g ∘ map f
map-compose {A} {B} {C} g f = 
  begin
    map (g ∘ f)
  ≡⟨⟩
    map ( λ (x : A) -> g (f x) )
    -- required evidence term (middle) for below extensionality:
    --
    -- ((x : List A) → map (λ x₁ → g (f x₁)) x ≡ map g (map f x)) →
    --            map (λ x → g (f x)) ≡ (λ x → map g (map f x))
  ≡⟨ extensionality 
        -- first stating which two functions we're asserting are extensionally eq, 
        -- that is: (map g ∘ f) and ( (map f) ∘ (map g) )
        (map (g ∘ f))  ((map g) ∘ (map f))  
        -- then supplying evidence that they are equal on all points (for all x : List A)
        (λ (xs : List A) -> sym (all-points-same-helper xs g f) )  
    ⟩
    (λ (xs : List A) -> map g (map f xs))
  ≡⟨⟩
    (map g) ∘ (map f)
  ∎
 -- f ∘ (map f)
-- λ (x : A) -> g (f x)
{- map : ∀ {A B : Set} -> (A -> B) -> List A -> List B 
    map {A} {B} f [] = []{B} -- (this also works: [] )
    map f (x :: xs)  = (f x) :: (map f xs)
-}
-- map f        : List A -> List B
--    > map ( λ (x : A) -> (f x) )

-- map g        : List B -> List C
--    > map ( λ (x : B) -> (g x) ) 

-- "prove the following relationship between map and append:" 

map-++-dist : ∀ {A B : Set} -> ∀ (f : A -> B) -> ∀ (xs ys : List A) 
  -> map f (xs ++ ys) ≡ map f xs ++ map f ys 
map-++-dist {A} {B} f [] ys = refl 
  {- -- longhand ver.
  begin 
    map f ([] ++ ys)
  ≡⟨⟩
    map f ys 
  ≡⟨⟩
    map f [] ++ map f ys
  ≡⟨⟩
    [] ++ map f ys 
  ∎-}
-- ?0 : map f (xs ++ []) ≡ map f xs ++ map f []
map-++-dist {A} {B} f xs [] =
  begin
    map f (xs ++ [])
  ≡⟨ cong (map f) (++-identity-r xs) ⟩
    map f xs
  ≡⟨ sym (++-identity-r (map f xs)) ⟩ -- allows us to go from (map f xs) to (map f xs) ++ (map f [])
  --  above: (map f xs ++ [] ≡ map f xs) ~> ( map f xs ≡ map f xs ++ [] )
    (map f xs) ++ (map f [])
  ≡⟨⟩ 
    (map f xs) ++ ([])
  ≡⟨ (++-identity-r (map f xs)) ⟩ 
    (map f xs)
    -- ++-identity-r : ∀ {A : Set} -> ∀ (xs : List A) -> xs ++ [] ≡ xs
  ≡⟨ sym (++-identity-r (map f xs)) ⟩
    map f xs ++ []
  ≡⟨⟩
    map f xs ++ map f []
  ∎
map-++-dist {A} {B} f (x :: xs) ys = 
  -- ?0 : map f ((x :: xs) ++ ys) ≡ map f (x :: xs) ++ map f ys
  begin
    map f ((x :: xs) ++ ys)
  ≡⟨⟩
    map f (x :: (xs ++ ys))
  ≡⟨⟩
    (f x) :: (map f (xs ++ ys))
    -- map-++-dist : .. map f (xs ++ ys) ≡ map f xs ++ map f ys 
  ≡⟨ cong ((f x) ::_ ) (map-++-dist f xs ys) ⟩ -- apply ind. hypothesis for (xs ++ ys)
    (f x) :: (map f xs) ++ (map f ys)  -- looking closer to the goal now..
  ≡⟨⟩ -- via 2nd defining eq of 'map' operator
    (map f (x :: xs)) ++ map f ys
  ∎
{- _++_ : ∀ {A : Set} -> List A -> List A -> List A 
  [] ++ ys        = ys 
  (x :: xs) ++ ys = x :: ( xs ++ ys )
-}
{- map : ∀ {A B : Set} -> (A -> B) -> List A -> List B 
    map {A} {B} f [] = []{B} -- (this also works: [] )
    map f (x :: xs)  = (f x) :: (map f xs)
-}

-- map-tree 

-- "Define a type of trees with leaves of type A and internal nodes 
-- of type B:"

data Tree (A B : Set) : Set where 
  leaf : A -> Tree A B 
  node : Tree A B -> B -> Tree A B -> Tree A B 

-- "define a suitable map operator over trees:"

map-tree : ∀ {A B C D : Set} 
  -> (f : A -> C) -> (g : B -> D) -> Tree A B -> Tree C D 
map-tree f g (leaf x)         = leaf (f x)
map-tree f g (node l item r)  = node (map-tree f g l) (g item) (map-tree f g r) 

-- l : Tree A B 
-- r : Tree A B 
-- (map-tree f g l) : Tree C D
-- (map-tree f g r) : Tree C D

-- fold

-- "Fold takes a binary operator and uses the operator to combine each 
-- of the elements of the list, taking the given value as the result for 
-- the empty list"

foldr : ∀ {A B : Set} -> (A -> B -> B) -> B -> List A -> B 
foldr _⊗_ e [] = e 
foldr _⊗_ e (x :: xs) = x ⊗ (foldr _⊗_ e xs)

_ : foldr _+_ 0 [ 1 , 2 , 3 , 4 ] ≡ 10
_ = 
  begin 
    foldr _+_ 0 ( 1 :: 2 :: 3 :: 4 :: [] )
  ≡⟨⟩
    1 + (foldr _+_ 0 ( 2 :: 3 :: 4 :: []))
  ≡⟨⟩
    1 + ( 2 + foldr _+_ 0 ( 3 :: 4 :: []) )
  ≡⟨⟩
    1 + 2 + ( 3 + (foldr _+_ 0 ( 4 :: []) ) )
  ≡⟨⟩
    1 + 2 + 3 + ( 4 + (foldr _+_ 0 []) )
  ≡⟨⟩
    1 + 2 + 3 + ( 4 + 0 )
  ≡⟨⟩
    10
  ∎

-- foldr requires time linear in the length of the list being folded
-- O(n)

-- use fold to define a function to find the product of a list of 
-- numbers. For example:

-- product [ 1 , 2 , 3 , 4 ] ≡ 24

product : List ℕ -> ℕ 
product lst with lst 
... | []            = foldr _*_ 0 []
... | xs@(_ :: xs₁) = foldr _*_ 1 xs
-- note: not sure why agda is giving me a weird yellow highlight
-- if the final case is just..:
-- ... | xs = foldr _*_ 1 xs

_ : product [ 2 , 3 , 2 ] ≡ 12
_ = 
  begin 
    product ( 2 :: 3 :: 2 :: [])
  ≡⟨⟩ 
    foldr (_*_) 1 ( 2 :: 3 :: 2 :: [])
  ≡⟨⟩ 
    (2 * foldr (_*_) 1 ( 3 :: 2 :: []))
  ≡⟨⟩ 
    2 * (3 * foldr (_*_) 1 ( 2 :: []) )
  ≡⟨⟩ 
    2 * (3 * (2 * foldr (_*_) 1 ([]) ) )
  ≡⟨⟩ 
    2 * (3 * (2 * 1 ) )
  ≡⟨⟩
    12
  ∎  

_ : product [] ≡ 0
_ = 
  begin 
    product []
  ≡⟨⟩
    foldr (_*_) 0 []
  ≡⟨⟩
    foldr (_*_) 0 []
  ∎ 

-- show that fold and append are related as follows:

{-
foldr : ∀ {A B : Set} -> (A -> B -> B) -> B -> List A -> B 
foldr _⊗_ e [] = e 
foldr _⊗_ e (x :: xs) = x ⊗ (foldr _⊗_ e xs)
-}
{- _++_ : ∀ {A : Set} -> List A -> List A -> List A 
  [] ++ ys        = ys 
  (x :: xs) ++ ys = x :: ( xs ++ ys )
-}

-- ++-identity-r : ∀ {A : Set} -> ∀ (xs : List A) -> xs ++ [] ≡ xs
foldr-++ : ∀ {A B : Set} -> ∀ (_⊗_ : A -> B -> B) -> ∀ (e : B)
  -> ∀ (xs ys : List A) 
  -> (foldr _⊗_ e (xs ++ ys)) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs 
foldr-++ {A} {B} _⊗_ e [] ys = refl
foldr-++ {A} {B} _⊗_ e xs [] = 
  -- ?0 : foldr _⊗_ e (xs ++ []) ≡ foldr _⊗_ (foldr _⊗_ e []) xs
  begin 
    foldr _⊗_ e (xs ++ [])
    -- cong (foldr _⊗_ e) (++-identity-r xs) --> (constructs term of shape:)-> foldr _⊗_ e (xs ++ []) 
  ≡⟨ cong (foldr _⊗_ e) (++-identity-r xs) ⟩ -- putting ? in the ⟨..⟩ gives equality: 
      --foldr _⊗_ e (xs ++ []) ≡ foldr _⊗_ (foldr _⊗_ e []) xs
      -- but this term 
      -- cong (foldr _⊗_ e) (++-identity-r xs)
      -- constructs this equality (recall cong tacks the (foldr (_⊗_ e)) on the front of each
      -- side of the raw term produced by:  xs ++ [] ≡ xs
      -- (foldr (_⊗_ e)) (xs ++ []) ≡ (foldr (_⊗_ e)) xs 
      -- which matches the state under the 'begin' block allowing us to rewrite to the goal shape
    foldr _⊗_ (foldr _⊗_ e []) xs  
  ∎
  ---  cong (foldr _⊗_ e) ++-identity-r xs c
foldr-++ {A} {B} _⊗_ e (x :: xs) ys = {!   !} 