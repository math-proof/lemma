import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealTurns
open StatMech StatMech.FrontierA


/--
[KWAdaptivePatchedData.idealRawEdge_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealTurns.lean)
-/
@[path]
private lemma idealRawEdge_ne_zero_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  ∀ j : Fin (n * (2 * (M + 1))), kwRawEdge patch.idealVertex j ≠ 0 := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealRawEdge_ne_zero patch

/--
[KWAdaptivePatchedData.idealTurnAdmissible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealTurns.lean)
-/
@[path]
private lemma idealTurnAdmissible_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0) :
-- imply
  ∀ j : Fin (n * (2 * (M + 1))), KWRawTurnAdmissible patch.idealVertex j := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealTurnAdmissible patch hcoords


-- created on 2026-10-23
