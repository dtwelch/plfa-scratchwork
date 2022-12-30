open import Data.Unit.Base
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Agda.Builtin.List renaming (List to Str)

data Tr (A : Set) : Set where
    Ω  : Tr A
    Jn : A -> Str (Tr A) -> Tr A

{-
// in Data.List
foldl : {A B : Set} -> (B -> A -> B) -> B -> List A -> B
foldl f z []        = z
foldl f z (x :: xs) = foldl f (f z x) xs
-}
N_C : {A : Set} -> Tr A -> ℕ
N_C Ω = 0
N_C (Jn x α) = {!   !} 
