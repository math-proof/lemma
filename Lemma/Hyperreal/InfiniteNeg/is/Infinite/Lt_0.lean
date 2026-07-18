import sympy.series.limits
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Hyperreal.InfiniteNeg.is.Infinite.Lt_0 |
| comm | Hyperreal.Infinite.is.InfiniteNeg.Lt_0 |
| mp   | Hyperreal.Infinite.of.InfiniteNeg.Lt_0 |
| mpr  | Hyperreal.InfiniteNeg.of.Infinite.Lt_0 |
-/
@[main, comm, mp and, mpr]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  x → -∞ ↔ x → ∞ ∧ x < 0 := by
-- proof
  aesop


-- created on 2025-12-25
