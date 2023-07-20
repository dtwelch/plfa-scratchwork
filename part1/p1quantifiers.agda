import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning

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

{-"
When a function is viewed as evidence of implication, both its argument 
and result are viewed as evidence, whereas when a dependent function is 
viewed as evidence of a universal, its argument is viewed as an element 
of a data type and its result is viewed as evidence of a proposition that 
depends on the argument. This difference is largely a matter of interpretation, 
since in Agda a value of a type and evidence of a proposition are 
indistinguishable." -}

-- universals distribute over conjunction
∀-distrib-× : 
    ∀ {A : Set} -> 
    ∀ {B C : A -> Set} -> 
        ( ∀ (a : A) -> B a × C a ) ≃ 
            (∀ (a : A) -> B a) × (∀ (a : A) -> C a)

∀-distrib-× {A} {B} {C} = 
    record {
        -- to: ((a : A) -> B a × C a) -> ((a : A) -> B a) × ((a : A) -> C a)
        to      = λ (f : ((a : A) -> B a × C a)) -> ⟨ (λ (a : A) -> proj₁ (f a)) , (λ (a : A) -> proj₂ (f a)) ⟩ ;

        from    = λ{ ⟨ lq , rq ⟩ -> λ (a : A) -> ⟨ (lq a) , (rq a) ⟩ }  ; 
        to∘from = λ{ ⟨ lq , rq ⟩ -> refl }  ;
        from∘to = λ (f : (a : A) -> B a × C a) -> refl 
    }

-- reproduced from connectives chapter:
case-⊎ : ∀ {A B C : Set}
    -> (A -> C)
    -> (B -> C)
    -> A ⊎ B
    -----------
    -> C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

-- goal (construct this): (a : A) -> B a ⊎ C a

⊎∀-implies-∀⊎ : 
    ∀ {A : Set} -> 
    ∀ {B C : A -> Set} ->
        (∀ (a : A) -> B a) ⊎ (∀ (a : A) -> C a) -> 
        (∀ (a : A) -> B a ⊎ C a)
-- more on patterns here: https://agda.readthedocs.io/en/v2.6.1/language/with-abstraction.html
⊎∀-implies-∀⊎ {A} {B} {C} h1 with h1 
...  | (inj₁ ba) = λ (a : A) -> (inj₁ {-B a-}{-C a-} (ba a))    
...  | (inj₂ ca) = λ (a : A) -> (inj₂ {-B a-}{-C a-} (ca a)) 

-- note, in each case above (matching either left (inj₁) or right (inj₂)),
-- we just need to construct the term B a and C a in each respective case...
-- Agda it seems implicitly constructs a type of the term for the opposite 
-- side of the disjunction being matched on..

-- consider the following type:
data Tri : Set where 
    aa : Tri 
    bb : Tri 
    cc : Tri 

-- let B be a type indexed by Tri, that is: B : Tri -> Set. Show that
-- ∀ (x : Tri) -> B x is isomorphic to B aa × B bb × B cc. Hint: you
-- will need to postulate a version of extensionality that works for 
-- dependent fns.

∀×-iso-to : ∀ {B : Tri -> Set} ->
    ((x : Tri) -> B x) -> B aa × (B bb × B cc)
∀×-iso-to {B} g = ⟨ (g aa) , ⟨ (g bb) , (g cc) ⟩ ⟩

∀×-iso-from : ∀ {B : Tri -> Set} -> 
    (B aa × (B bb × B cc)) -> ((x : Tri) -> B x)
∀×-iso-from {B} ⟨ Baa , ⟨ Bbb , Bcc ⟩ ⟩ = 
    λ{ aa -> Baa ; bb -> Bbb ; cc -> Bcc } -- : (x : Tri) -> B x

-- a pseudocode-ish more explicit form of defining eq for ∀×-iso-from:
-- ∀×-iso-from {B} ⟨ Baa , ⟨ Bbb , Bcc ⟩ ⟩ = 
--    λ (x : Tri) -> match x with
--                        |  aa -> Baa
--                        |  bb -> Bbb
--                        |  cc -> Ccc 

postulate
    -- dependent extensionality
    dep-extensionality : ∀ {A : Set} {B : A -> Set} 
            -> ∀ (f g : (x : A) -> (B x))
                -> (∀ (x : A) -> f x ≡ g x)
            ----------------------------
            -> f ≡ g

-- from prior ch on connectives:
η-× : ∀ {A B : Set} (w : A × B) -> ⟨ proj₁ w , proj₂ w ⟩ ≡ w 
η-× {A} {B} (⟨_,_⟩ x y) = refl

{-
∀×-iso-from∘to : 
    ∀ {B : Tri -> Set} ->
    ∀ (f : (x : Tri) -> B x) -> 
        ∀×-iso-from (∀×-iso-to f) ≡ f
∀×-iso-from∘to {B} f =
    dep-extensionality  (∀×-iso-from (∀×-iso-to f)) (f)
    (λ (x : Tri) -> ( (λ (x : Tri) -> (λ { aa → refl ; bb -> refl ; cc -> refl  }) x) )) 
-}

∀×-iso-from∘to : {B : Tri → Set} → (f : ∀ (x : Tri) → B x)
  → (∀×-iso-from ∘ ∀×-iso-to) f ≡ f
∀×-iso-from∘to {B} f = dep-extensionality {Tri} {B} (∀×-iso-from (∀×-iso-to f)) (f) 
       λ{ aa -> refl; bb -> refl; cc -> refl} 
    
    -- ((λ { aa -> refl ; bb -> refl ;  }) x)

    -- need: (x : Tri) → ∀×-iso-from (∀×-iso-to f) x ≡ f x

-- λ (x : Tri) -> η-× ∀×-iso-from (∀×-iso-to f) 
-- λ (x : Tri) -> η-× (∀×-iso-to f)       : (x : Tri) -> ∀×-iso-to f ≡ ∀×-iso-to f

     --  λ (x : Tri) -> ∀×-iso-from (η-× (∀×-iso-to f) )  !}
-- need to construct:
-- ((x : Tri) -> ∀×-iso-from (∀×-iso-to f) x ≡ f x)
    
-- ∀×-iso-to   : ((x : Tri) -> B x)     -> B aa × (B bb × B cc)
-- ∀×-iso-from : (B aa × (B bb × B cc)) -> ((x : Tri) -> B x)

--      dep-extensionality (∀×-iso-from (∀×-iso-to f))  f
-- type is:
--  ((x : Tri) -> ∀×-iso-from (∀×-iso-to f) x ≡ f x) ->
--    ∀×-iso-from (∀×-iso-to f) ≡ f

∀×-iso : ∀ {B : Tri -> Set} -> 
    (∀ (x : Tri) -> B x) ≃ B aa × B bb × B cc 
∀×-iso {B} = record {
        to      = ∀×-iso-to   ; 
        from    = ∀×-iso-from ;
        -- ?0 : (y : B aa × B bb × B cc) -> ∀×-iso-to (∀×-iso-from y) ≡ y
        to∘from = λ (y : B aa × B bb × B cc) -> refl ;

        -- ?1 : (x : (x₁ : Tri) -> B x₁) -> ∀×-iso-from (∀×-iso-to x) ≡ x
        from∘to = ∀×-iso-from∘to
    }

-- existential quantification is encoded by the following inductive type:

data Σ (A : Set) (B : A -> Set) : Set where
    ⟨_,_⟩ : (x : A) -> B x -> Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x -> Bx) = Σ[ x ∈ A ] Bx

-- "evidence that Σ[ x ∈ A ] B x holds is of the form 
--  ⟨ M , N ⟩ where M is a term of type A, and N is evidence 
--  that B M holds."

-- "product apps _×_ are a special case of existentials in 
--  which the second component does not depend on the variable drawn
--  from the first component"

-- "A common notation for existentials is ∃ (analogous to ∀ for universals). 
-- We follow the convention of the Agda standard library, and reserve this 
-- notation for the case where the domain of the bound variable is left implicit:"

∃ : ∀ {A : Set} (B : A -> Set) -> Set 
∃ {A} B = Σ A B 

∃-syntax = ∃
syntax ∃-syntax (λ x -> B) = ∃[ x ] B 

-- "the special syntax is available only when the identifier 
--  ∃-syntax is imported. We will tend to use this syntax, since
--  it is shorter and more familiar"



