module Array_Template where 
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning

open import Relation.Nullary.Decidable.Core using (isYes)
open import Data.Bool using (Bool; true; false; if_then_else_; T; not )
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc; _≟_; _+_)
open import Data.Product using (∃-syntax; _×_)
open import Data.String using (String; _==_)
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Agda.Builtin.Char

open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Data.Maybe

{-
    public static void doubleSwapFirst(StaticArray<Integer> a) {
        // ensures a = #a
        int lb = a.lowerBound();
        Integer e = a.replace(lb, 5); // replace lower with 5
        a.replace(lb, e); // put it back
    }

    Remember a;
        int lb = a.lowerBound();
        int e  = a.replace(lb, 5);
        a.replace(lb, e);
    Confirm a = #a;
    ->
        ...
        int e = a.replace(lb, 5);
    Confirm ( λ x : ℕ -> if x = lb then #e 
                         else           #a(x) ) = #a       -- omitting bounds for now
    -> 
        ...
    Confirm ( λ x : ℕ -> if x = lb then e 
                         else           a(x) ) = #a 
    ->
        ...
    Confirm ( λ x : ℕ -> if x = lb then a(lb) 
                         else ( if q = lb then e else a(q) ) ) = #a 
    -> 
        ...
        int lb = a.lowerBound();
    Confirm ( λ x : ℕ -> if      x = lb then a(lb) 
                         else if x = lb then e 
                         else                a(x) ) = #a  
    ->
        ...
        int lb = a.lowerBound();
    Confirm ( λ x : ℕ -> if   x = lb then a(lb) 
                         else             a(x) ) = #a   
    ->
    Remeber a;
    Confirm ( λ x : ℕ -> if     x = lowerBound then a(lowerBound) 
                         else                       a(x) ) = #a   
    -> 
    Confirm ( λ x : ℕ -> if     x = lowerBound then a(lowerBound) 
                         else                       a(x) ) = a

someVc: 
    ⊢ (λ x : ℕ -> if x = lowerBound then a(lowerBound)) 
                   else                   a(x)         ) ≡ a
-}

-- first, defining constants
Entry : Set 
Entry = ℕ

postulate 
  extensionality : ∀ {A B : Set} (f g : A -> B)
    -> (∀ (x : A) -> f x ≡ g x)
    ----------------------------
    -> f ≡ g

vc1 :   ∀ {lowerBound upperBound : ℕ} ->  
        ∀ {a : ℕ -> Entry} -> 
            (λ (x : ℕ) -> 
                if isYes (x ≟ lowerBound) then (a lowerBound)
                else (a x)) ≡ a
vc1 {lowerBound} {upperBound} {a} = {!   !} 

-- ((x : ℕ) →
-- (if isYes (x ≟ lowerBound) then a lowerBound else a x) ≡ a x) -> 
-- (λ x → if isYes (x ≟ lowerBound) then a lowerBound else a x) ≡ a

{-
In Agda, a piecewise function with three alternatives can be expressed using nested 
if-then-else constructs within a lambda expression. Ex: 

piecewise : (ℕ → A) → (ℕ → A) → (ℕ → A) → ℕ → A
piecewise f g h = λ x → if condition1 x then f x 
                        else if condition2 x then g x  // NOTE THE else if
                        else h x
-} 

-- example
f : ℕ -> ℕ 
f x = x + 1

g : ℕ -> ℕ
g x = if isYes (x ≟ 0) then 1 else f x 

eq-on-all-points : ∀ (x : ℕ) -> f x ≡ g x
eq-on-all-points x = 
    begin 
        f x
    ≡⟨ {!   !} ⟩
        {!   !}
    ∎ 

lemma : g ≡ f
lemma = {!   !} 