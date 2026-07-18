import sympy.series.limits
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Hyperreal.InfinitePos.is.Infinite.Gt_0 |
| comm | Hyperreal.Infinite.is.InfinitePos.Gt_0 |
| mp   | Hyperreal.Infinite.of.InfinitePos.Gt_0 |
| mpr  | Hyperreal.InfinitePos.of.Infinite.Gt_0 |
-/
@[main, comm, mp and, mpr]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  x → +∞ ↔ x → ∞ ∧ x > 0 := by
-- proof
  aesop


-- created on 2025-12-25
