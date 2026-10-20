import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Metric
open scoped Finset


/--
[unitDistNum_eq_distanceMultiplicity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Metric.lean)
-/
@[path]
private lemma unitDistNum_eq_distanceMultiplicity_eq
  [MetricSpace X]
  {s : Finset X} :
-- imply
  unitDistNum s = distanceMultiplicity s 1 := by
-- proof
  apply unitDistNum_eq_distanceMultiplicity s

/--
[unitDistNum_le_choose_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Metric.lean)
-/
@[path]
private lemma unitDistNum_le_choose_two_eq
  [MetricSpace X]
  {X}
  {s : Finset X} :
-- imply
  unitDistNum s ≤ (#s).choose 2 := by
-- proof
  apply unitDistNum_le_choose_two X s


-- created on 2026-10-20
