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