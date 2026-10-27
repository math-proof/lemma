import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealHomotopyTurns
open StatMech StatMech.FrontierA


/--
[KWAdaptivePatchedData.idealAxisHomotopy_turnAdmissible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealHomotopyTurns.lean)
-/
@[path]
private lemma idealAxisHomotopy_turnAdmissible_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {t : ℝ}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
  (ht : t ∈ Icc (0 : ℝ) 1) :
-- imply
  ∀ j : Fin (n * (2 * (M + 1))), KWRawTurnAdmissible (patch.idealAxisHomotopyVertex t) j := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealAxisHomotopy_turnAdmissible patch hcoords ht


-- created on 2026-10-23
