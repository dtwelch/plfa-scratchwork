module p1negation where 

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)
open import plfa.part1.Isomorphism using (_≃_; extensionality)

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

{-
postulate 
  extensionality : ∀ {A B : Set} (f g : A -> B)
    -> (∀ (x : A) -> f x ≡ g x)
    ----------------------------
    -> f ≡ g

-}
assimilation : ∀ {A : Set} (¬x ¬x' : ¬ A) -> ¬x ≡ ¬x'
assimilation {A} ¬x ¬x' = extensionality λ (x : A) -> ⊥-elim (¬x' x)

<-irreflexive : ∀ (n : ℕ) -> ¬ (n < n) 
<-irreflexive zero = λ ()
<-irreflexive (suc x) ih = {!   !}  
-- h1: ¬ (suc n < suc n)
-- h2:  (suc n < suc n) 

-- ⊥-elim h1 h2  to produce ⊥ ?