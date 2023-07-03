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

-- evidenence that A × B holds is of the form ⟨ M , N ⟩ 
-- where M provides evidence that A and N provides evidence that B holds 

proj₁ : ∀ {A B : Set} 
    -> A × B 
    --------
    -> A
proj₁ {A} {B} (⟨_,_⟩ x y) = x
-- nicer way of writing (that uses the mixfix below):
-- proj₁ {A} {B} ⟨ x , y ⟩  = {!   !}
-- the {A} and {B} bit there can also be removed 
-- (necessary only if you want to explicitly annotate 
--  types in various spots in the defining equations)
