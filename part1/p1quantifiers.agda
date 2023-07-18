import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.part1.Isomorphism using (_≃_; extensionality)
open import Function using (_∘_)

-- universals 

-- "given a variable x : A and a proposition B x containing x as a free var,
-- proposition ∀ (x : A) -> B x holds if for each term M of type A, B M holds.
-- where B M stands for proposition B x with each free occurrence of x replaced
-- M."

∀-elim : ∀ {A : Set} -> {B : A -> Set}
    -> (L : ∀ (x : A) -> B x)
    -> (M : A)
    -------------------------
    -> B M 
∀-elim {A} {B} ∀x:A,Bx m = ∀x:A,Bx m

{-
When a function is viewed as evidence of implication, both its argument 
and result are viewed as evidence, whereas when a dependent function is 
viewed as evidence of a universal, its argument is viewed as an element 
of a data type and its result is viewed as evidence of a proposition that 
depends on the argument. 

This difference is largely a matter of interpretation, since in Agda a 
value of a type and evidence of a proposition are indistinguishable.
-}

-- universals distribute over conjunction
∀-distrib-× : 
    ∀ {A : Set} -> 
    ∀ {B C : A -> Set} -> 
        ( ∀ (a : A) -> B a × C a ) ≃ (∀ (a : A) -> B a) × (∀ (a : A) -> C a)

∀-distrib-× {A} {B} {C} = 
    record {
        -- to: ((a : A) -> B a × C a) -> ((a : A) -> B a) × ((a : A) -> C a)
        to      = λ (f : ((a : A) -> B a × C a)) -> ⟨ (λ (a : A) -> proj₁ (f a)) , (λ (a : A) -> proj₂ (f a)) ⟩ ;

        from    = λ{ ⟨ lq , rq ⟩ -> λ (a : A) -> ⟨ (lq a) , (rq a) ⟩ }  ; 
        to∘from = λ{ ⟨ lq , rq ⟩ -> refl }  ;
        from∘to = λ (f : (a : A) -> B a × C a) -> refl 
    }

⊎∀-implies-∀⊎ : 
    ∀ {A : Set} -> 
    ∀ {B C : A -> Set} ->
        (∀ (a : A) -> B a) ⊎ (∀ (a : A) -> C a) -> ∀ (a : A) -> (B a) ⊎ (C a)
-- goal (construct this): (a : A) -> B a ⊎ C a

-- q1⊎q2 : ((a : A) → B a) ⊎ ((a : A) → C a)
-- h1 : A
⊎∀-implies-∀⊎ {A} {B} {C} = λ{ (inj₁ ba) (inj₂ ca) -> λ (x : A) -> {!   !}  }