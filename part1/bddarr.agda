-- Concept for bounded arrays 
{- Concept Bdd_Array_Template (type Entry       ; 
                               Integer Lower_Bd ;
                               Integer Upper_Bd)
    uses Integer_Theory;
    requires 0 <= Lower_Bd <= Upper_Bd 
        which_entails Lower_Bd, Upper_Bd : ℕ

    Type family Array is modeled by ℤ -> Entry 
        exemplar A;
        initialization
            ensures ∀ (x : A) -> Entry.Is_Initial(A i)

    Operation Swap_Entry (updates A   : Static_Array ;
                          updates e   : Entry ;
                          evaluates i : Integer)
        requires Lower_Bound ≤ i ≤ Upper_Bound
        ensures e = # A(i) ∧ A = λ (j : ℤ) -> 
            if j = i then #e 
            else #A(j) 
-}

module bddarr where 

