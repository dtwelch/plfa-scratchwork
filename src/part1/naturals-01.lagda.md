## P101: Natural numbers

Natural numbers are an inductive data type named 
ℕ where 0, 1, 2 ... are inhabitants of ℕ

```agda
--------
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
- and another `suc n` that takes one ℕ and maps it to its immediate successor.
