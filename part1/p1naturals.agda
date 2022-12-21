module p1naturals where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ


    
{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + n = n                -- base case
(suc m) + n = suc (m + n)   -- ind hypo

+0 : ∀ (x : ℕ) -> x + zero ≡ x
+0 zero = refl
+0 (suc x) rewrite (+0 x) = refl
    
_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩ -- is shorthand for
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩ -- is shorthand for
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩    -- inductive case
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩    -- base case
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩    -- is longhand for
  5
  ∎

_*'_ : ℕ -> ℕ -> ℕ
zero *' n = zero
(suc m) *' n = n + (m *' n)

{-
_monus_ : ℕ -> ℕ -> ℕ
m      monus zero  = m          -- mo ctor 1
zero   monus suc n = zero       -- mo ctor 2
suc m monus suc n  = m monus n  -- mo ctor 3

_ : 3 monus 2
_ =
  begin
    3 monus 2
  ≡⟨⟩
    2 monus 1
  ≡⟨⟩
    1 monus 0
  ≡⟨⟩
    0
  ∎
-}
 
