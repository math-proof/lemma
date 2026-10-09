import sympy.sets.sets
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Nat.Le.Le.is.Le.Min |
| mp | Nat.Le.Min.of.Le.Le |
| mpr | Nat.Le.Le.of.Le.Min |
-/
@[path, mp, mpr]
private lemma main
  {x a b : ℝ} :
-- imply
  x ≤ a ∧ x ≤ b ↔ x ≤ min a b := by
-- proof
  exact le_min_iff.symm


-- created on 2022-01-03
-- updated on 2026-10-07
