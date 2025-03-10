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

When ***2reading*** inference rules, everything above the horizontal line are called 
hypotheses, and a single judgement below the line is called the conclusion.

The first rule is the base case, it has no hypotheses. Its conclusion assers that 
`suc 0` is a natural number. The second rule is the inductive case. 