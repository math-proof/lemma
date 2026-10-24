import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamLemmaOneAlgebra
open StatMech StatMech.FrontierA


/--
[grahamSimonComparison_algebra](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamLemmaOneAlgebra.lean)
-/
@[path]
private lemma grahamSimonComparison_algebra_eq
  {a b c d e x y v : Real}
-- given
  (hv : 0 < v)
  (hb : 0 <= b)
  (hx : 0 <= x)
  (hy : 0 <= y)
  (hvar : v = 1 - b ^ 2)
  (hghs : 2 * b * x * y <= v * (d * x + a * y - (e - c * b)))
  (hbridgeA : 0 <= a * v - b * x)
  (hbridgeD : 0 <= d * v - b * y) :
-- imply
  v * (c - a * d) <= c - e * b := by
-- proof
  apply StatMech.FrontierA.grahamSimonComparison_algebra a b c d e x y v hv hb hx hy hvar hghs hbridgeA hbridgeD


-- created on 2026-10-23
