import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.TriHexFKExternalWeight
open Finset StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triHexFK_terminalWeightedSum_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKExternalWeight.lean)
-/
@[path]
private lemma triHexFK_terminalWeightedSum_identity_eq
  {q y0 y1 y2 y0Star y1Star y2Star : Real}
  {external : ThreeTerminalConnectivity → Real}
-- given
  (h0 : y0 * y0Star = q)
  (h1 : y1 * y1Star = q)
  (h2 : y2 * y2Star = q)
  (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0) :
-- imply
  (y0 * y1 * y2) * starFKTerminalWeightedSum q y0Star y1Star y2Star external = q ^ 2 * triangleFKTerminalWeightedSum y0 y1 y2 external := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFK_terminalWeightedSum_identity h0 h1 h2 hsurface external

/--
[triHexFK_terminalWeightedRatio_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKExternalWeight.lean)
-/
@[path]
private lemma triHexFK_terminalWeightedRatio_eq_eq
  {q y0 y1 y2 y0Star y1Star y2Star : Real}
  {external observable : ThreeTerminalConnectivity → Real}
-- given
  (hq : q ≠ 0)
  (hyprod : y0 * y1 * y2 ≠ 0)
  (h0 : y0 * y0Star = q)
  (h1 : y1 * y1Star = q)
  (h2 : y2 * y2Star = q)
  (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0) :
-- imply
  starFKTerminalWeightedRatio q y0Star y1Star y2Star external observable = triangleFKTerminalWeightedRatio y0 y1 y2 external observable := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFK_terminalWeightedRatio_eq hq hyprod h0 h1 h2 hsurface external observable


-- created on 2026-10-23
