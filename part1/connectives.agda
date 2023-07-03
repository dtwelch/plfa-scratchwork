module connectives where 

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality; _⇔_)
open plfa.part1.Isomorphism.≃-Reasoning

-- given two propositions A and B, the conjunction A × B holds if both A and B hold. We formalize
-- this idea by declaring a suitable datatype:

data _×_ (A B : Set) : Set where 
    ⟨_,_⟩ : 
           A
        -> B
        --------
        -> A × B 