import sympy.sets.sets
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.GeAbs.is.Or |
| mpr | Int.GeAbs.of.Or |
-/
@[main, mpr]
private lemma main
  {x a : ℝ} :
-- imply
  |x| ≥ a ↔ x ≤ -a ∨ x ≥ a := by
-- proof
  exact le_abs'


-- created on 2022-01-07
-- updated on 2026-10-07
