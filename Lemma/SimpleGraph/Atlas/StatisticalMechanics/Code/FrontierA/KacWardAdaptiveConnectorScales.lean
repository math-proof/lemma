import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveConnectorScales
open StatMech StatMech.FrontierA


/--
[KWFiniteSimplePolygon.exists_smallAdaptiveConnectorScales](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveConnectorScales.lean)
-/
@[path]
private lemma exists_smallAdaptiveConnectorScales_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {r : ℝ}
-- given
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
  (hr : 0 < r) :
-- imply
  Nonempty (KWSmallAdaptiveConnectorScales polygon r) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_smallAdaptiveConnectorScales polygon hcoords hr


-- created on 2026-10-23
