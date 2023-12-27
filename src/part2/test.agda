module test where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong)
open Eq.≡-Reasoning

open import Relation.Nullary.Decidable.Core using (isYes)
open import Data.Nat using (ℕ; zero; suc; _+_; _≟_)
open import Relation.Nullary using (yes ; no)

open import Data.Bool using (Bool; true; false; if_then_else_; T; not )

-- example : ∀ (x : ℕ) -> (if isYes (x ≟ 0) then 0 else 0) ≡ 0 
-- example x = case  

example : ℕ -> ℕ -> Bool
example m n with (m ≟ n)
... | yes p = true  
... | no ¬p = false

example2 : ∀ (x : ℕ) -> ((if x ≟ 0 then true else false) ≡ false -> x ≢ 0)
example2 x eq = ? 
{-
  case x ≡ 0 of {
    (yes xIsZero) -> contradiction refl xIsZero;
    (no xNotZero) -> xNotZero
  }

-} 