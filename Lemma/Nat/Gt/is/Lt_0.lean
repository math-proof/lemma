import sympy.sets.sets
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Nat.Gt.is.Lt_0 |
| mp | Nat.Lt_0.of.Gt |
| mpr | Nat.Gt.of.Lt_0 |
-/
@[path, mp, mpr]
private lemma main
  {x y : ℝ} :
-- imply
  x > y ↔ y - x < 0 := by
-- proof
  exact sub_neg.symm


-- created on 2023-06-19
-- updated on 2026-10-07
