import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

-- composition
_∘_ : ∀ {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)
(g ∘ f) x  = g (f x)

-- can also do it this way:
_∘'_ : ∀ {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)
g ∘' f  =  λ x -> g (f x)

-- extensionality
postulate 
    extensionality : ∀ {A B : Set} (f g : A -> B)
        -> (∀ (x : A) -> f x ≡ g x )
        ----------------------------
        -> f ≡ g

_+'_ : ℕ -> ℕ -> ℕ
m +' zero = m 
m +' (suc n) = suc (m +' n)
