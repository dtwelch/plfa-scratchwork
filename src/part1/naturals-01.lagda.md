## Natural numbers

Natural numbers are an inductive data type named 
ℕ where 0, 1, 2 ... are inhabitants of ℕ

```agda
--------
zero : ℕ

m : ℕ
--------
suc m : ℕ
```

Here is the definition of natural numbers in Agda:

```agda
data ℕ : Set where 
    zero : ℕ
    suc  : ℕ -> ℕ
```