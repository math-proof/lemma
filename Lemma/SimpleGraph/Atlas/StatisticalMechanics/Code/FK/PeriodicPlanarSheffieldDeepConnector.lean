import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepConnector
open Filter MeasureTheory Set StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.deepOpenExitedJoinedBoundaryArmEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepConnector.lean)
-/
@[path]
private lemma deepOpenExitedJoinedBoundaryArmEvent_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r R c d : Real}
  {L U : Finset V} :
-- imply
  MeasurableSet (E.deepOpenExitedJoinedBoundaryArmEvent r R c d L U) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.deepOpenExitedJoinedBoundaryArmEvent_measurableSet E r R c d L U

/--
[PeriodicPlaneEmbedding.deepOpenExitedJoinedBoundaryArmEvent_witnesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepConnector.lean)
-/
@[path]
private lemma deepOpenExitedJoinedBoundaryArmEvent_witnesses_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {omega : ConfigSpace (Sym2 V)}
  {r R c d : Real}
  {L U : Finset V}
-- given
  (h : omega ∈ E.deepOpenExitedJoinedBoundaryArmEvent r R c d L U) :
-- imply
  ∃ x ∈ L, (P.cluster omega x).Infinite ∧ ∃ b ∈ E.lowerBoundaryRayVertices r c, ∃ z : V, P.graph.Adj b z ∧ z ∉ E.rightHalfPlaneVertices r ∧ omega s(b, z) = true ∧ omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) x b ∧ ∃ y ∈ U, (P.cluster omega y).Infinite ∧ ∃ u ∈ E.upperBoundaryRayVertices r d, ∃ w : V, P.graph.Adj u w ∧ w ∉ E.rightHalfPlaneVertices r ∧ omega s(u, w) = true ∧ omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) y u ∧ omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices R) x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.deepOpenExitedJoinedBoundaryArmEvent_witnesses E h

/--
[PeriodicPlaneEmbedding.deepOpenExitedJoinedBoundaryArmEvent_measureReal_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepConnector.lean)
-/
@[path]
private lemma deepOpenExitedJoinedBoundaryArmEvent_measureReal_ge_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r R c d : Real}
  {L U : Finset V} :
-- imply
  mu.real (E.infiniteOpenBoundaryConnectionTo r (L : Set V) (E.lowerBoundaryRayVertices r c)) + mu.real (E.infiniteOpenBoundaryConnectionTo r (U : Set V) (E.upperBoundaryRayVertices r d)) - mu.real (E.halfPlanePairMergeErrorUnion R L U) - 1 ≤ mu.real (E.deepOpenExitedJoinedBoundaryArmEvent r R c d L U) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.deepOpenExitedJoinedBoundaryArmEvent_measureReal_ge E mu r R c d L U

/--
[PeriodicPlaneEmbedding.deepOpenExitedJoinedBoundaryArmEvent_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepConnector.lean)
-/
@[path]
private lemma deepOpenExitedJoinedBoundaryArmEvent_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r R c d : Nat → Real}
  {L U : Nat → Finset V}
-- given
  (hlower : Tendsto (fun n => mu.real (E.infiniteOpenBoundaryConnectionTo (r n) (L n : Set V) (E.lowerBoundaryRayVertices (r n) (c n)))) atTop (nhds 1))
  (hupper : Tendsto (fun n => mu.real (E.infiniteOpenBoundaryConnectionTo (r n) (U n : Set V) (E.upperBoundaryRayVertices (r n) (d n)))) atTop (nhds 1))
  (hmerge : Tendsto (fun n => mu.real (E.halfPlanePairMergeErrorUnion (R n) (L n) (U n))) atTop (nhds 0)) :
-- imply
  Tendsto (fun n => mu.real (E.deepOpenExitedJoinedBoundaryArmEvent (r n) (R n) (c n) (d n) (L n) (U n))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.deepOpenExitedJoinedBoundaryArmEvent_tendsto_one E mu r R c d L U hlower hupper hmerge


-- created on 2026-10-23
