module

public section


/--
| attributes | lemma |
| :---: | :---: |
| path | Nat.Le_Min.is.Le.Le |
| comm | Nat.Le.Le.is.Le_Min |
| mp | Nat.Le.Le.of.Le_Min |
| mpr | Nat.Le_Min.of.Le.Le |
-/
@[comm, mp, mpr]
public theorem Nat.Le_Min.is.Le.Le
  [LinearOrder α]
-- given
  (x a b : α) :
-- imply
  x ≤ a ⊓ b ↔ x ≤ a ∧ x ≤ b := by
-- proof
  constructor <;>
  · 
    intros
    simp_all


-- created on 2025-09-29
