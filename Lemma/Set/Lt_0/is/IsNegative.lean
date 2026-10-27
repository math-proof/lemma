import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Set.Lt_0.is.IsNegative |
| mpr | Set.Lt_0.of.IsNegative |
-/
@[path, mpr]
private lemma main
  {x : ℝ} :
-- imply
  x < 0 ↔ x ∈ Set.Iio 0 :=
-- proof
  Set.mem_Iio.symm


-- created on 2026-10-07
