import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealPhaseHomotopy
open StatMech StatMech.FrontierA


/--
[KWRawTurnAdmissible.angle_ne_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealPhaseHomotopy.lean)
-/
@[path]
private lemma angle_ne_pi_eq
  {m : ℕ}
  [NeZero m]
  {vertex : Fin m → ℂ}
  {i : Fin m}
-- given
  (hedge : ∀ j : Fin m, kwRawEdge vertex j ≠ 0)
  (h : KWRawTurnAdmissible vertex i) :
-- imply
  (Complex.arg (kwRawEdge vertex (i + 1)) : Real.Angle) - (Complex.arg (kwRawEdge vertex i) : Real.Angle) ≠ (Real.pi : Real.Angle) := by
-- proof
  apply StatMech.FrontierA.KWRawTurnAdmissible.angle_ne_pi hedge h

/--
[KWAdaptivePatchedData.idealAxisHomotopy_angle_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealPhaseHomotopy.lean)
-/
@[path]
private lemma idealAxisHomotopy_angle_continuous_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {k : Fin (n * (2 * (M + 1)))}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0) :
-- imply
  ContinuousOn (fun t : ℝ ↦ (Complex.arg (kwRawEdge (patch.idealAxisHomotopyVertex t) k) : Real.Angle)) (Icc 0 1) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealAxisHomotopy_angle_continuous patch hcoords k

/--
[KWAdaptivePatchedData.idealAxisHomotopy_phaseProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealPhaseHomotopy.lean)
-/
@[path]
private lemma idealAxisHomotopy_phaseProduct_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0) :
-- imply
  (∏ k : Fin (n * (2 * (M + 1))), kwVectorTurnPhase (kwRawEdge patch.idealVertex k) (kwRawEdge patch.idealVertex (k + 1))) = ∏ k : Fin (n * (2 * (M + 1))), kwVectorTurnPhase (kwRawEdge patch.vertex k) (kwRawEdge patch.vertex (k + 1)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealAxisHomotopy_phaseProduct patch hcoords

/--
[KWAdaptivePatchedData.idealAxisHomotopy_phaseCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealPhaseHomotopy.lean)
-/
@[path]
private lemma idealAxisHomotopy_phaseCycle_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0) :
-- imply
  kwVectorPhaseCycle (List.ofFn (kwRawEdge patch.idealVertex)) = kwVectorPhaseCycle (List.ofFn (kwRawEdge patch.vertex)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealAxisHomotopy_phaseCycle patch hcoords


-- created on 2026-10-23
