module p1negation where 

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
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
    -> (A -> B) -- parentheses here very important 
                -- (otherwise f pattern below would just be A -- not A -> B)
    ---------
    -> (¬ B -> ¬ A)
contraposition f notB x = notB (f x)

_≢_ : ∀ {A : Set} -> A -> A -> Set 
_≢_ x y = ¬ (x ≡ y)

