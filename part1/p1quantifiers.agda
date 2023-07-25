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
    (∀ (x : Tri) -> B x) -> B aa × (B bb × B cc)
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

∀×-iso-from∘to : {B : Tri -> Set} -> (f : ∀ (x : Tri) -> B x)
  -> (∀×-iso-from ∘ ∀×-iso-to) f ≡ f
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
syntax ∃-syntax (λ x {-: A-} -> B) = ∃[ x ] B 

-- "the special syntax is available only when the identifier 
--  ∃-syntax is imported. We will tend to use this syntax, since
--  it is shorter and more familiar"

∃-elim : ∀ {A : Set} -> ∀ {B : A -> Set} -> ∀ {C : Set} 
    -> (∀ (x : A) -> (B x) -> C)
    -> ∃[ x ] B x 
    ----------------------------
    -> C 
∃-elim {A} {B} {C} f ⟨ x , y ⟩ =  (f x) y
-- (f x)    : B x -> C
-- (f x) y  : C         
-- ( y -- of type: B x -- comes from the existential being pattern matched on)

-- some helper lemmas/corollaries
∀∃-cur-to : ∀ {A : Set} -> ∀ {B : A -> Set} -> ∀ {C : Set} 
    -> (∀ (x : A) -> B x -> C) -> ( ∃[ x ] B x -> C )
∀∃-cur-to {A} {B} {C} f ⟨ x , body ⟩ = (f x) body -- goal: C

-- goal: (x : A) -> B x -> C
∀∃-cur-from : ∀ {A : Set} -> ∀ {B : A -> Set} -> ∀ {C : Set} 
    -> ( ∃[ x ] B x -> C ) -> (∀ (x : A) -> B x -> C)
∀∃-cur-from {A} {B} {C} g x body = g ⟨ x , body ⟩

∀∃-cur-to∘from : ∀ {A : Set} -> ∀ {B : A -> Set} -> ∀ {C : Set} 
    -> ∀ (y : ∃-syntax B -> C) -> ∀∃-cur-to (∀∃-cur-from y) ≡ y
∀∃-cur-to∘from {A} {B} {C} f = extensionality λ{ ⟨ x , body ⟩ -> refl  }
-- ?0 : (x : ∃-syntax B) → ∀∃-cur-to (∀∃-cur-from f) x ≡ f x

∀∃-currying : ∀ {A : Set} -> ∀ {B : A -> Set} -> ∀ {C : Set}
    -> (∀ (x : A) -> B x -> C) ≃ ( ∃[ x ] B x -> C )
∀∃-currying {A} {B} {C} = 
    record {
        to          = ∀∃-cur-to         ;
        from        = ∀∃-cur-from       ;
        to∘from     = ∀∃-cur-to∘from    ;
        from∘to     = λ{ f -> refl }    
    }

-- "show that existentials distribute over disjunction"

-- ?1 : ∃-syntax (λ x → B x ⊎ C x) → ∃-syntax B ⊎ ∃-syntax C
∃-dist-⊎-to : ∀ {A : Set} -> ∀ {B C : A -> Set} ->
    ∃-syntax (λ x -> B x ⊎ C x) -> (∃-syntax B) ⊎ (∃-syntax C)
∃-dist-⊎-to {A} {B} {C} ex with ex 
... | ⟨ x , (inj₁ bodyL) ⟩ = inj₁ ⟨ x , bodyL ⟩ -- Σ A B ⊎ Σ A C
... | ⟨ x , (inj₂ bodyR) ⟩ = inj₂ ⟨ x , bodyR ⟩ -- Σ A B ⊎ Σ A C

∃-dist-⊎-from : ∀ {A : Set} -> ∀ {B C : A -> Set} ->
    ∃-syntax B ⊎ ∃-syntax C -> ∃-syntax (λ x -> B x ⊎ C x)
∃-dist-⊎-from {A} {B} {C} u with u 
-- ⟨ a , λ (x : A) -> ? ⟩
... | (inj₁ ⟨ x , body ⟩) = ⟨ x , (inj₁ body) ⟩  -- Σ A (λ x -> B x ⊎ C x)   ⟨ x , body ⟩ on lhs is a ∃ expr of type: Σ A B
... | (inj₂ ⟨ x , body ⟩) = ⟨ x , (inj₂ body) ⟩  -- Σ A (λ x -> B x ⊎ C x)    ⟨ x , body ⟩ constructs an ∃ of type: Σ A C

∃-distrib-⊎ : ∀ {A : Set} -> ∀ {B C : A -> Set} ->
    ∃[ x ] (B x ⊎ C x) ≃ ( ∃[ x ] B x) ⊎ (∃[ x ] C x )
∃-distrib-⊎ {A} {B} {C} = 
    record {
        to      = ∃-dist-⊎-to   ;
        from    = ∃-dist-⊎-from ;

        -- goal: (y: ∃-syntax B ⊎ ∃-syntax C) → ∃-dist-⊎-to (∃-dist-⊎-from y) ≡ y
        -- extensionality {A} : 
        --      {B = B₁: Set} {f g : A -> B₁} → ((x : A) → f x ≡ g x) → f ≡ g

        -- (inj₁ b) : ∃-syntax B
        -- b above can be matched with ⟨ x , y ⟩ (for example)

        -- to∘from = λ { (inj₁ ⟨ x , y ⟩ ) -> refl ; (inj₂ ⟨ x , y ⟩ ) -> ? } gives: 
        -- ?0: ∃-dist-⊎-to (∃-dist-⊎-from (inj₂ ⟨ x , y ⟩)) ≡ inj₂ ⟨ x , y ⟩
        to∘from = λ { (inj₁ ⟨ x , y ⟩ ) -> refl ; (inj₂ ⟨ x , y ⟩ ) -> refl }  ;

        -- (x: ∃-syntax (λ x₁ -> B x₁ ⊎ C x₁)) -> ∃-dist-⊎-from (∃-dist-⊎-to x) ≡ x
        from∘to = λ { ⟨ x , (inj₁ b) ⟩ -> refl ; ⟨ x , (inj₂ b) ⟩ -> refl } 
    }

-- "Show that an existential of conjunctions implies a 
--  conjunction of existentials:"
∃×-implies-×∃ : ∀ {A : Set} -> ∀ {B C : A -> Set} -> 
    ∃[ m ] (B m × C m) -> (∃[ m ] B m) × (∃[ m ] C m)
--                       ∃  m -- B m -- × -- B m
∃×-implies-×∃ {A} {B} {C} ⟨ m , ⟨ bm     ,    cm ⟩ ⟩ = 
    ⟨ ⟨ m , bm ⟩ , ⟨ m , cm ⟩ ⟩ -- goal: ∃-syntax B × ∃-syntax C

-- does the existential quantifier ∃ distribute over the 
-- conjunction (_×_) operator?
--
-- ans: no, the converse gives us the hypothesis:
-- 'there exists some value m₁ : A such that B m₁ holds, AND
--  there exists some other value m₂ : A such that C m holds..'
--
-- but it is not necessarily the case that there exists a value m₃ : A
-- such that B m₃ and C m₃ both hold.. the hypothesis doesn't give enough 
-- to construct the term we need since the bound vars m₁ and m₂ for 
-- each ∃ term are different. This precludes building a term of the shape:
--   ∃[ m₃ ] (B m₃ × C m₃) 
-- (we only have (B m₁) and  (C m₂) to work with)

-- ×∃-implies-∃× : ∀ {A : Set} -> ∀ {B C : A -> Set} -> 
--    (∃[ m ] B m) × (∃[ m ] C m) -> ∃[ m ] (B m × C m) <-- bogus 

-- "Let Tri and B be as in Exercise ∀-×. Show that ∃[ x ] B x is isomorphic
--  to B aa ⊎ B bb ⊎ B cc."

∃⊎-iso-to : {B : Tri -> Set} -> 
    (∃[ x ] B x) -> (B aa ⊎ B bb ⊎ B cc)
∃⊎-iso-to {B} ⟨ aa , body ⟩ = inj₁ {-B aa-}{-B bb ⊎ B cc-} body 
∃⊎-iso-to {B} ⟨ bb , body ⟩ = inj₂ {-B aa-}{-B bb ⊎ B cc-} (inj₁ body)
∃⊎-iso-to {B} ⟨ cc , body ⟩ = inj₂ {-B aa-}{-B bb ⊎ B cc-} (inj₂ body)

∃⊎-iso : ∀ {B : Tri -> Set} -> 
    (∃[ x ] B x) ≃ (B aa ⊎ B bb ⊎ B cc)
∃⊎-iso {B} = 
    record {

        to      = ∃⊎-iso-to ;
        from    = {!   !} ;
        to∘from = {!   !} ;
        from∘to = {!   !}
    }