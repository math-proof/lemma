import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSplitPhaseGauge
open StatMech StatMech.FrontierA


/--
[triangularTorusSplitDartDirection_nonbacktracking](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitPhaseGauge.lean)
-/
@[path]
private lemma triangularTorusSplitDartDirection_nonbacktracking_eq
  {L : Nat}
  [Fact (2 < L)]
  {d e : (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)).Dart}
-- given
  (hconnect : d.snd = e.fst)
  (hne : d.edge ≠ e.edge) :
-- imply
  triangularTorusSplitDartDirection L e ≠ triangularTorusDirectionReverse (triangularTorusSplitDartDirection L d) := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitDartDirection_nonbacktracking L d e hconnect hne

/--
[triangularTorusPortDirection_of_matching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitPhaseGauge.lean)
-/
@[path]
private lemma triangularTorusPortDirection_of_matching_eq
  {L : Nat}
  [Fact (2 < L)]
  {p q : KWDartPort (triangularTorusGraph L)}
-- given
  (hmatching : kwDartOfPort (triangularTorusGraph L) q = (kwDartOfPort (triangularTorusGraph L) p).symm) :
-- imply
  triangularTorusGraphDartDirection L (kwDartOfPort (triangularTorusGraph L) q) = triangularTorusDirectionReverse (triangularTorusGraphDartDirection L (kwDartOfPort (triangularTorusGraph L) p)) := by
-- proof
  apply StatMech.FrontierA.triangularTorusPortDirection_of_matching L hmatching

/--
[triangularTorusSplit_refinedPhase_eq_gauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitPhaseGauge.lean)
-/
@[path]
private lemma triangularTorusSplit_refinedPhase_eq_gauge_eq
  {L : Nat}
  [Fact (2 < L)]
  {rho : Complex}
  {d e : (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)).Dart}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hconnect : d.snd = e.fst)
  (hne : d.edge ≠ e.edge) :
-- imply
  triangularTorusGraphPhase (3 * L) rho 1 1 ((triangularTorusSplitEmbedHom L).mapDart d) ((triangularTorusSplitEmbedHom L).mapDart e) = kwPhaseGauge (triangularTorusSplitPhaseGauge L rho) (kwLocalAngularSplitPhase (triangularTorusLocalAngularData L rho hrho)) d e := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplit_refinedPhase_eq_gauge L rho hrho d e hconnect hne

/--
[triangularTorusSplitEmbedCycleDartLoop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitPhaseGauge.lean)
-/
@[path]
private lemma triangularTorusSplitEmbedCycleDartLoop_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : KWDartPort (triangularTorusGraph L)}
  {p : (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)).Walk root root}
  {k : Fin p.darts.length} :
-- imply
  let hlen : (triangularTorusSplitEmbedWalk L p).darts.length = p.darts.length := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbedCycleDartLoop L p k

/--
[triangularTorusSplit_cyclePhaseProduct_eq_refined](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitPhaseGauge.lean)
-/
@[path]
private lemma triangularTorusSplit_cyclePhaseProduct_eq_refined_eq
  {L : Nat}
  [Fact (2 < L)]
  {rho : Complex}
  {root : KWDartPort (triangularTorusGraph L)}
  {p : (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)).Walk root root}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hp : p.IsCycle) :
-- imply
  let q := triangularTorusSplitEmbedWalk L p letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ letI : NeZero q.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr (triangularTorusSplitEmbedWalk_isCycle L p hp).not_nil))⟩ kwLoopPhaseProduct (kwLocalAngularSplitPhase (triangularTorusLocalAngularData L rho hrho)) (kwGraphCycleDartLoop p) = kwLoopPhaseProduct (triangularTorusGraphPhase (3 * L) rho 1 1) (kwGraphCycleDartLoop q) := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplit_cyclePhaseProduct_eq_refined L rho hrho p hp

/--
[triangularTorus_localAngularSplitShiftedCyclePhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitPhaseGauge.lean)
-/
@[path]
private lemma triangularTorus_localAngularSplitShiftedCyclePhase_eq
  {L : Nat}
  [Fact (2 < L)]
  {rho : Complex}
-- given
  (hrho : rho ^ 4 = Complex.I) :
-- imply
  KWLocalAngularSplitShiftedCyclePhase (triangularTorusLocalAngularData L rho hrho) (kwOrderedSplitEdgeClass (triangularTorusSurfaceEdgeClass L)) (triangularTorusSurfaceSpin 0 0) := by
-- proof
  apply StatMech.FrontierA.triangularTorus_localAngularSplitShiftedCyclePhase L rho hrho


-- created on 2026-10-23
