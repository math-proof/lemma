import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearHomotopyReduction.Part2
open StatMech StatMech.FrontierA


/--
[kwVectorTurnPhase_pos_scales](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearHomotopyReduction.lean)
-/
@[path]
private lemma kwVectorTurnPhase_pos_scales_eq
  {s t : ℝ}
  {z w : ℂ}
-- given
  (hs : 0 < s)
  (ht : 0 < t)
  (hz : z ≠ 0)
  (hw : w ≠ 0) :
-- imply
  kwVectorTurnPhase ((s : ℂ) * z) ((t : ℂ) * w) = kwVectorTurnPhase z w := by
-- proof
  apply StatMech.FrontierA.kwVectorTurnPhase_pos_scales s t hs ht z w hz hw

/--
[KWRectilinearPhaseHomotopy.angle_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearHomotopyReduction.lean)
-/
@[path]
private lemma angle_continuous_eq
  {n m : ℕ}
  [NeZero n]
  [NeZero m]
  {source : KWFiniteSimplePolygon n}
  {k : Fin m}
-- given
  (h : KWRectilinearPhaseHomotopy source) :
-- imply
  ContinuousOn (fun t ↦ (Complex.arg ((h.polygon t).edgeVector k) : Real.Angle)) (Icc 0 1) := by
-- proof
  apply StatMech.FrontierA.KWRectilinearPhaseHomotopy.angle_continuous h k

/--
[KWRectilinearPhaseHomotopy.phaseProduct_zero_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearHomotopyReduction.lean)
-/
@[path]
private lemma phaseProduct_zero_eq_one_eq
  {n m : ℕ}
  [NeZero n]
  [NeZero m]
  {source : KWFiniteSimplePolygon n}
-- given
  (h : KWRectilinearPhaseHomotopy source) :
-- imply
  (∏ k : Fin m, kwVectorTurnPhase ((h.polygon 0).edgeVector k) ((h.polygon 0).edgeVector (k + 1))) = ∏ k : Fin m, kwVectorTurnPhase ((h.polygon 1).edgeVector k) ((h.polygon 1).edgeVector (k + 1)) := by
-- proof
  apply StatMech.FrontierA.KWRectilinearPhaseHomotopy.phaseProduct_zero_eq_one h

/--
[KWRectilinearPhaseHomotopy.source_phaseCycle_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearHomotopyReduction.lean)
-/
@[path]
private lemma source_phaseCycle_eq_neg_one_eq
  {n m : ℕ}
  [NeZero n]
  [NeZero m]
  {source : KWFiniteSimplePolygon n}
-- given
  (h : @KWRectilinearPhaseHomotopy n m _ _ source) :
-- imply
  kwVectorPhaseCycle source.edgeList = -1 := by
-- proof
  apply StatMech.FrontierA.KWRectilinearPhaseHomotopy.source_phaseCycle_eq_neg_one h

/--
[kwFiniteSimplePolygonPhaseSign_of_rectilinearizable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearHomotopyReduction.lean)
-/
@[path]
private lemma kwFiniteSimplePolygonPhaseSign_of_rectilinearizable_eq
-- given
  (hrect : KWFiniteSimplePolygonRectilinearizable) :
-- imply
  KWFiniteSimplePolygonPhaseSign := by
-- proof
  apply StatMech.FrontierA.kwFiniteSimplePolygonPhaseSign_of_rectilinearizable hrect


-- created on 2026-10-23
