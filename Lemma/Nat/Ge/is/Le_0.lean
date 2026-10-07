import sympy.sets.sets
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.Ge.is.Le_0 |
| mp | Nat.Le_0.of.Ge |
| mpr | Nat.Ge.of.Le_0 |
-/
@[main, mp, mpr]
private lemma main
  {x y : ℝ} :
-- imply
  x ≥ y ↔ y - x ≤ 0 := by
-- proof
  exact sub_nonpos.symm


-- created on 2023-06-19
-- updated on 2026-10-07
