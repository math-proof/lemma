import sympy.sets.sets
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Nat.LeMax.is.And.Le |
| mp | Nat.And.Le.of.LeMax |
| mpr | Nat.LeMax.of.And.Le |
-/
@[path, mp, mpr]
private lemma main
  {x a b : ℝ} :
-- imply
  max a b ≤ x ↔ a ≤ x ∧ b ≤ x :=
-- proof
  max_le_iff


-- created on 2026-10-07
