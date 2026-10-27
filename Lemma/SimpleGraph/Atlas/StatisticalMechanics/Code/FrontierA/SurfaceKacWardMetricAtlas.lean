import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardMetricAtlas.Part4
open Finset SimpleGraph StatMech StatMech.FrontierA StatMech.FrontierA.ClosedMetricFlatSurfaceGraphAtlas


/--
[kwAngleTurnPhase_sq_eq_toCircle_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardMetricAtlas.lean)
-/
@[path]
private lemma kwAngleTurnPhase_sq_eq_toCircle_div_eq
  {a b : Real.Angle} :
-- imply
  kwAngleTurnPhase a b ^ 2 = (b.toCircle : Complex) / (a.toCircle : Complex) := by
-- proof
  apply StatMech.FrontierA.kwAngleTurnPhase_sq_eq_toCircle_div a b

/--
[kwAngleTurnPhase_reverse_add_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardMetricAtlas.lean)
-/
@[path]
private lemma kwAngleTurnPhase_reverse_add_pi_eq
  {a b : Real.Angle}
-- given
  (hne : b - a ≠ Real.pi) :
-- imply
  kwAngleTurnPhase (b + Real.pi) (a + Real.pi) = (kwAngleTurnPhase a b)⁻¹ := by
-- proof
  apply StatMech.FrontierA.kwAngleTurnPhase_reverse_add_pi a b hne

/--
[kwClosedWalkAngleRotationNumber_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardMetricAtlas.lean)
-/
@[path]
private lemma kwClosedWalkAngleRotationNumber_spec_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {root : V}
  {p : G.Walk root root}
-- given
  (angle : G.Dart -> Real.Angle)
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ (∑ k, (angle (kwGraphCycleDartLoop p (k + 1)) - angle (kwGraphCycleDartLoop p k)).toReal : Real) = (kwClosedWalkAngleRotationNumber angle p : Real) * (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierA.kwClosedWalkAngleRotationNumber_spec angle p hp

/--
[developedTurnSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardMetricAtlas.lean)
-/
@[path]
private lemma developedTurnSum_eq
  {g : Nat}
  {Cone : Type v}
  [Fintype Cone]
  [DecidableEq Cone]
  {atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G}
  {root : V}
  {p : G.Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ (∑ k, (atlas.angle (kwGraphCycleDartLoop p (k + 1)) - atlas.angle (kwGraphCycleDartLoop p k)).toReal : Real) = (atlas.rotationNumber p : Real) * (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierA.ClosedMetricFlatSurfaceGraphAtlas.developedTurnSum atlas p hp

/--
[direction_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardMetricAtlas.lean)
-/
@[path]
private lemma direction_ne_zero_eq
  {g : Nat}
  {Cone : Type v}
  [Fintype Cone]
  [DecidableEq Cone]
  {atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G}
  {dart : G.Dart} :
-- imply
  atlas.direction dart ≠ 0 := by
-- proof
  apply StatMech.FrontierA.ClosedMetricFlatSurfaceGraphAtlas.direction_ne_zero atlas dart

/--
[direction_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardMetricAtlas.lean)
-/
@[path]
private lemma direction_reverse_eq
  {g : Nat}
  {Cone : Type v}
  [Fintype Cone]
  [DecidableEq Cone]
  {atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G}
  {dart : G.Dart} :
-- imply
  atlas.direction dart.symm = -atlas.direction dart := by
-- proof
  apply StatMech.FrontierA.ClosedMetricFlatSurfaceGraphAtlas.direction_reverse atlas dart

/--
[phase_sq_eq_direction_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardMetricAtlas.lean)
-/
@[path]
private lemma phase_sq_eq_direction_div_eq
  {g : Nat}
  {Cone : Type v}
  [Fintype Cone]
  [DecidableEq Cone]
  {atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G}
  {dart next : G.Dart} :
-- imply
  atlas.phase dart next ^ 2 = atlas.direction next / atlas.direction dart := by
-- proof
  apply StatMech.FrontierA.ClosedMetricFlatSurfaceGraphAtlas.phase_sq_eq_direction_div atlas dart next

/--
[phase_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardMetricAtlas.lean)
-/
@[path]
private lemma phase_reverse_eq
  {g : Nat}
  {Cone : Type v}
  [Fintype Cone]
  [DecidableEq Cone]
  {atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G}
  {dart next : G.Dart}
-- given
  (hadj : G.DartAdj dart next)
  (hne : dart.edge ≠ next.edge) :
-- imply
  atlas.phase next.symm dart.symm = (atlas.phase dart next)⁻¹ := by
-- proof
  apply StatMech.FrontierA.ClosedMetricFlatSurfaceGraphAtlas.phase_reverse atlas dart next hadj hne


-- created on 2026-10-23
