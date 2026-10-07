import sympy.sets.sets
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.Gt.is.Gt_0 |
| mpr | Nat.Gt.of.Gt_0 |
-/
@[main, mpr]
private lemma main
  {x y : ℝ} :
-- imply
  x > y ↔ x - y > 0 := by
-- proof
  exact sub_pos.symm


-- created on 2023-04-18
-- updated on 2026-10-07
