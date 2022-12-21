module p1equality where

data _≡_ {A : Set} (x : A) : A -> Set where 
    refl : x ≡ x 

infix 4 _≡_

sym : ∀ {A : Set} (x y : A)
    -> x ≡ y 
    ---------
    -> y ≡ x
sym b a h1 =  {!   !}


≡-trans : ∀ {A : Set} (x y z : A)
    -> x ≡ y
    -> y ≡ z 
    ---------
    -> x ≡ z
≡-trans a b c refl refl = refl 

