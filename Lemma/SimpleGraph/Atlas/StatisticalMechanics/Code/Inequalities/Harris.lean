import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
open StatMech


/--
[harris_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Harris.lean)
-/
@[path]
private lemma harris_inequality_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace E)}
-- given
  (hp : p ≤ 1)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B ≤ (bernoulliProductMeasure (E := E) p hp).real (A ∩ B) := by
-- proof
  apply StatMech.harris_inequality hp hA hB


-- created on 2026-10-23
