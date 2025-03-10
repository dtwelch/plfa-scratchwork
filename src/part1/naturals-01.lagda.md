## P101: Natural numbers

Natural numbers are an inductive data type named ℕ where 0, 1, 2 ... are inhabitants of ℕ

```text
----------
zero : ℕ

m : ℕ
--------
suc m : ℕ
```

Here is the inductive type modeling natural numbers in Agda:

```agda
data ℕ : Set where 
    zero : ℕ
    suc  : ℕ -> ℕ
```

The constructor offers two "constructors" that produce a ℕ. These are:
-  `zero` which allows us to construct the value `zero` of the natural numbers
- and another `suc n` that takes one ℕ and maps it to its immediate successor (also something of type ℕ).

### **exercise `seven` (practice)**

```agda
seven : ℕ 
seven = suc (suc (suc (suc (suc (suc (suc zero))))))
```

When reading inference rules, everything above the horizontal line are called 
hypotheses, and a single judgement below the line is called the conclusion.

The first rule is the base case, it has no hypotheses. Its conclusion assers that 
`suc 0` is a natural number. The second rule is the inductive case. 

```agda
-- {-# BUILTIN NATURAL ℕ #-}
```

Tells agda that ℕ corresponds to the natural numbers, and hence one is permitted
to use 0 as shorthand for zero. I don't want to use this, so I'll be disabling it 
for now.

```agda
import Relation.Binary.PropositionalEquality as Eq 
open Eq using (_≡_; refl) 
open Eq.≡-Reasoning using (begin_; step-≡-∣; _∎)
```

Here is the definition of addition in agda:
```agda
_+_ : ℕ -> ℕ -> ℕ 
_+_ zero n = n
_+_ (suc m) n = suc (m + n)
```
This definition has both a base case and inductive case. The base case says 
that adding zero to a numner, `zero + n` returns that number, `n`. The 
inductive case says that adding the successor of a number to another number, `(suc m) + n` returns the successor 
of adding two numbers, `suc (m + n)`. 

#### Exercise `+-example` (practice)

