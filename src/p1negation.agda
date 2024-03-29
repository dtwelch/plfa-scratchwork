module p1negation where 

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂ ) renaming (_,_ to ⟨_,_⟩)
open import plfa.part1.Isomorphism using (_≃_; extensionality)
open import Function using (_∘_)

-- given a proposition A, the negation ¬ A holds if A cannot hold... 
-- idea: make negation to be the same thing as implication of false..

¬_ : Set -> Set
¬_ A = A -> ⊥

-- "reductio ad absurdum" if assuming A leads to the conlusion ⊥ (an absurdity)
-- then it must be the case that ¬ A 

-- evidence that ¬ A holds is of the form:

-- λ x : T -> N

-- where N is a term of type ⊥ containing a free variable x of type A. 

-- "In other words, evidence that ¬ A holds is a function that converts evidence
-- that A holds into evidence that ⊥ holds"

infix 3 ¬_
-- so ¬ A × ¬ B parses as (¬ A) × (¬ B) and ¬ m ≡ n as ¬ (m ≡ n).

¬-elim : ∀ {A : Set} 
    -> ¬ A 
    -> A 
    -------
    -> ⊥
¬-elim {A} notA a = notA a 

¬¬-intro : ∀ {A : Set} 
    -> A 
    -----
    -> ¬ ¬ A 
¬¬-intro {A} a = λ (notA : (¬ A)) -> notA a  
-- note: this works too (notice the notA pattern we're matching on)
-- ¬¬-intro {A} a notA = notA a 
-- this is happening since appearances of the const operator ¬_ .. are treated like 
-- functions of type: A -> ⊥

¬¬¬-elim : ∀ {A : Set}
    -> ¬ (¬ (¬ A))  -- h1
    ----------
    -> ¬ A 
¬¬¬-elim {A} h1 a = h1 (¬¬-intro a) 

-- contraposition
contraposition : ∀ {A B : Set } 
    -> (A -> B) -- parentheses very important here
                -- (otherwise f pattern below would match on A -- not A -> B)
    ---------
    -> ( ¬ B -> ¬ A )
    -- f  : A -> B
    -- ¬B : ¬ B
    -- a  : A
contraposition f ¬B a = (¬-elim ¬B (f a))

-- inequality
_≢_ : ∀ {A : Set} -> A -> A -> Set 
_≢_ x y = ¬ (x ≡ y)

something : 1 ≢ 2
something = λ ()

-- zero is not the successor of any number
peano : ∀ { m : ℕ } -> zero ≢ (suc m)
peano = λ ()

{- postulate 
    extensionality : ∀ {A B : Set} (f g : A -> B)
        -> (∀ (x : A) -> f x ≡ g x)
        ----------------------------
        -> f ≡ g
-}
assimilation : ∀ {A : Set} (¬x ¬x' : ¬ A) -> ¬x ≡ ¬x'
assimilation {A} ¬x ¬x' = extensionality λ (x : A) -> ⊥-elim (¬x' x)

infix 4 _<'_

data _<'_ : ℕ -> ℕ -> Set where

  z<s : ∀ {n : ℕ}
    ---------------
    -> zero <' suc n

  s<s : ∀ {m n : ℕ}
    -> m <' n
    ----------------
    -> suc m <' suc n

{- ¬-elim : ∀ {A : Set} 
        -> ¬ A 
        -> A 
        -------
        -> ⊥
-}

<-irreflexive : ∀ (n : ℕ) -> ¬ (n <' n) 
<-irreflexive zero = λ ()
-- someone is asserting that for any x ∈ ℕ, ¬ (suc x <' suc x), so 
-- we do an inductive proof and construct an 'assumption' term of the 
-- shape x <' x called h1, we'll use this to show (by way of contradiction) that 
-- the successor cannot hold; base case 'zero' matches absurd

--                                          ¬ (x <' x)       x <' x
                                          ---------------   --------
<-irreflexive (suc x) (s<s  h1) = ¬-elim (<-irreflexive x)     h1      -- h1 : x <' x here

-- ¬-elim ¬A A 
-- so an application of ¬-elim, given witnesses/evidence of both ¬A and A, produces 
-- bottom: ⊥

-- note: reproduced from previous ch. 
-- todo: maybe replace w/ std. library version?
case-⊎ : ∀ {A B C : Set}
  -> (A -> C)
  -> (B -> C)
  -> A ⊎ B
  -------------
  -> C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

--  'to' helper:
⊎-dual-×-to : ∀ {A B : Set} -> ¬ (A ⊎ B) -> (¬ A) × (¬ B)
⊎-dual-×-to {A} {B} ¬a⊎b = ⟨ (λ (a : A) ->  ¬a⊎b (inj₁ a)) , (λ (b : B) -> ¬a⊎b (inj₂ b)) ⟩ 

-- (λ (a : A) -> ¬a⊎b (inj₁ a)) forms type: (a : A) -> ⊥
-- (λ (b : B) -> ¬a⊎b (inj₂ b)) forms type: (b : B) -> ⊥

-- the a product is formed out of the top two lines using _,_
-- (λ (a : A) -> ¬a⊎b (inj₁ a)) , (λ (b : B) -> ¬a⊎b (inj₂ b))

-- 'from' helper:
⊎-dual-×-from : ∀ {A B : Set} -> (¬ A) × (¬ B) -> ¬ (A ⊎ B)
⊎-dual-×-from {A} {B} ¬A×¬B A⊎B = case-⊎ (proj₁ ¬A×¬B) (proj₂ ¬A×¬B) A⊎B  
-- case-⊎ (proj₁ ¬A×¬B) (proj₂ ¬A×¬B) A⊎B -- allows us to conclude: ⊥ ? (update: yes)
-- (proj₁ ¬A×¬B) : ¬ A
-- (proj₂ ¬A×¬B) : ¬ B

casehelper : ∀ {A B : Set} -> (f : (A ⊎ B) -> ⊥) -> (x : A ⊎ B) ->
     case-⊎ (f ∘ inj₁) (f ∘ inj₂) x ≡ f x
casehelper {A} {B} f (inj₁ x) = refl
casehelper {A} {B} f (inj₂ x) = refl

⊎-dual-×-from∘to : ∀ {A B : Set} -> (y : ¬ (A ⊎ B)) -> ⊎-dual-×-from (⊎-dual-×-to y) ≡ y
⊎-dual-×-from∘to {A} {B} y = (extensionality ∘ casehelper) y   

⊎-dual-× : ∀ {A B : Set} -> ¬ (A ⊎ B) ≃ (¬ A) × (¬ B) 
⊎-dual-× {A} {B} = 
    record {
        to      = ⊎-dual-×-to ;
        from    = ⊎-dual-×-from ; -- ⊎-dual-×-from

        -- (y : ¬ A × ¬ B) -> ⊎-dual-×-to (⊎-dual-×-from y) ≡ y
        to∘from = λ (y : (¬ A × ¬ B)) -> refl ; 
        from∘to = ⊎-dual-×-from∘to
    }