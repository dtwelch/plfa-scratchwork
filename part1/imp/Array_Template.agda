module Array_Template where 
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning

open import Data.Bool using (Bool; true; false; if_then_else_; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_)
open import Data.String using (String; _==_; _≟_)
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Agda.Builtin.Char

open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Data.Maybe
{-

In Agda, a piecewise function with three alternatives can be expressed using nested 
if-then-else constructs within a lambda expression. Ex: 

piecewise : (ℕ → A) → (ℕ → A) → (ℕ → A) → ℕ → A
piecewise f g h = λ x → if condition1 x then f x 
                        else if condition2 x then g x  // NOTE THE else if
                        else h x
-}