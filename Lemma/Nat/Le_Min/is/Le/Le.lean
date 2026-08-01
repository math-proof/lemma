import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.Le_Min.is.Le.Le |
| comm | Nat.Le.Le.is.Le_Min |
| mp | Nat.Le.Le.of.Le_Min |
| mpr | Nat.Le_Min.of.Le.Le |
-/
@[main, comm, mp, mpr]
private lemma main
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
