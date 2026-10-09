import sympy.sets.sets
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Int.Le.is.Le_0 |
| mp | Int.Le_0.of.Le |
| mpr | Int.Le.of.Le_0 |
-/
@[path, mp, mpr]
private lemma main
  {x y : ℝ} :
-- imply
  x ≤ y ↔ x - y ≤ 0 := by
-- proof
  exact sub_nonpos.symm


-- created on 2023-04-18
-- updated on 2026-10-07
