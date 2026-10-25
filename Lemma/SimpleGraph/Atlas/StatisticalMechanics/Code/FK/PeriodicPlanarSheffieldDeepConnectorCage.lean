import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepConnectorCage
open Filter MeasureTheory Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair


/--
[PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepConnectorCage.lean)
-/
@[path]
private lemma finiteDeepOpenExitedJoinedBoundaryArmEvent_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r R c d : Real}
  {width : Nat}
  {L U : Finset V} :
-- imply
  MeasurableSet (E.finiteDeepOpenExitedJoinedBoundaryArmEvent r R c d width L U) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent_measurableSet E r R c d width L U

/--
[PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent_witnesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepConnectorCage.lean)
-/
@[path]
private lemma finiteDeepOpenExitedJoinedBoundaryArmEvent_witnesses_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {omega : ConfigSpace (Sym2 V)}
  {r R c d : Real}
  {width : Nat}
  {L U : Finset V}
-- given
  (h : omega ∈ E.finiteDeepOpenExitedJoinedBoundaryArmEvent r R c d width L U) :
-- imply
  ∃ x ∈ L, (P.cluster omega x).Infinite ∧ ∃ b ∈ E.lowerBoundaryRayVertices r c, omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) x b ∧ ∃ y ∈ U, (P.cluster omega y).Infinite ∧ ∃ u ∈ E.upperBoundaryRayVertices r d, omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) y u ∧ omega ∈ P.connectedWithinSet (E.rightHalfPlaneStripVertices R width) x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent_witnesses E h

/--
[PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent_subset_verticalCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepConnectorCage.lean)
-/
@[path]
private lemma finiteDeepOpenExitedJoinedBoundaryArmEvent_subset_verticalCrossing_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {B r R c d cRight dRight : Real}
  {width : Nat}
  {L U : Finset V}
-- given
  (hB : ∀ {v w : V} (hvw : P.graph.Adj v w) (t) (i : Fin 2), |E.coordinates (E.edgeArc hvw t - E.vertex v) i| ≤ B)
  (hB0 : 0 ≤ B)
  (hgap : cRight + B < dRight)
  (hLbelow : ∀ x ∈ L, E.vertexCoord x 1 < cRight)
  (hUabove : ∀ y ∈ U, dRight < E.vertexCoord y 1) :
-- imply
  E.finiteDeepOpenExitedJoinedBoundaryArmEvent r R c d width L U ⊆ E.verticalCrossingEvent R (R + width) cRight dRight := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent_subset_verticalCrossing E hB hB0 hgap hLbelow hUabove

/--
[PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent_measureReal_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepConnectorCage.lean)
-/
@[path]
private lemma finiteDeepOpenExitedJoinedBoundaryArmEvent_measureReal_ge_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r R c d : Real}
  {width : Nat}
  {L U : Finset V} :
-- imply
  mu.real (E.infiniteOpenBoundaryConnectionTo r (L : Set V) (E.lowerBoundaryRayVertices r c)) + mu.real (E.infiniteOpenBoundaryConnectionTo r (U : Set V) (E.upperBoundaryRayVertices r d)) - mu.real (E.halfPlaneStripPairMergeErrorUnion R width L U) - 1 ≤ mu.real (E.finiteDeepOpenExitedJoinedBoundaryArmEvent r R c d width L U) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent_measureReal_ge E mu r R c d width L U

/--
[PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepConnectorCage.lean)
-/
@[path]
private lemma finiteDeepOpenExitedJoinedBoundaryArmEvent_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r R c d : Nat → Real}
  {width : Nat → Nat}
  {L U : Nat → Finset V}
-- given
  (hlower : Tendsto (fun n => mu.real (E.infiniteOpenBoundaryConnectionTo (r n) (L n : Set V) (E.lowerBoundaryRayVertices (r n) (c n)))) atTop (nhds 1))
  (hupper : Tendsto (fun n => mu.real (E.infiniteOpenBoundaryConnectionTo (r n) (U n : Set V) (E.upperBoundaryRayVertices (r n) (d n)))) atTop (nhds 1))
  (hmerge : Tendsto (fun n => mu.real (E.halfPlaneStripPairMergeErrorUnion (R n) (width n) (L n) (U n))) atTop (nhds 0)) :
-- imply
  Tendsto (fun n => mu.real (E.finiteDeepOpenExitedJoinedBoundaryArmEvent (r n) (R n) (c n) (d n) (width n) (L n) (U n))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent_tendsto_one E mu r R c d width L U hlower hupper hmerge

/--
[finiteDeepOpenExitedJoinedBoundaryArmEvent_subset_threeCrossingCageEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepConnectorCage.lean)
-/
@[path]
private lemma finiteDeepOpenExitedJoinedBoundaryArmEvent_subset_threeCrossingCageEvent_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {B rPrimal Rdeep rDual Rcage C D0 A Tbottom Ttop c d : Real}
  {width : Nat}
  {L U : Finset V}
-- given
  (hBp : ∀ {v w : V} (hvw : P.graph.Adj v w) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hvw t - D.primalEmbedding.vertex v) i| ≤ B)
  (hB0 : 0 ≤ B)
  (hRightGap : C - 4 * B + B < D0 + 4 * B)
  (hLbelow : ∀ x ∈ L, D.primalEmbedding.vertexCoord x 1 < C - 4 * B)
  (hUabove : ∀ y ∈ U, D0 + 4 * B < D.primalEmbedding.vertexCoord y 1)
  (hwidth : A + 4 * B = Rdeep ∧ Rdeep + width = Rcage - 4 * B)
  (hLowerCorridor : D.primalEmbedding.infiniteOpenBoundaryConnectionTo rPrimal (L : Set V) (D.primalEmbedding.lowerBoundaryRayVertices rPrimal c) ⊆ D.primalEmbedding.horizontalCrossingEvent (rDual - 5 * B) (Rcage + 5 * B) (C + 4 * B) (Tbottom - 4 * B))
  (hUpperCorridor : D.primalEmbedding.infiniteOpenBoundaryConnectionTo rPrimal (U : Set V) (D.primalEmbedding.upperBoundaryRayVertices rPrimal d) ⊆ D.primalEmbedding.horizontalCrossingEvent (rDual - 5 * B) (Rcage + 5 * B) (Ttop + 4 * B) (D0 - 4 * B)) :
-- imply
  D.primalEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent rPrimal Rdeep c d width L U ⊆ threeCrossingCageEvent D B rDual Rcage C D0 A Tbottom Ttop := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.finiteDeepOpenExitedJoinedBoundaryArmEvent_subset_threeCrossingCageEvent D hBp hB0 hRightGap hLbelow hUabove hwidth hLowerCorridor hUpperCorridor

/--
[finiteDeepOpenExitedJoinedBoundaryArmEvent_disjoint_boundaryBand_of_subset_cage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepConnectorCage.lean)
-/
@[path]
private lemma finiteDeepOpenExitedJoinedBoundaryArmEvent_disjoint_boundaryBand_of_subset_cage_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {B rPrimal Rdeep rDual Rcage C D0 A Tbottom Ttop c d : Real}
  {width : Nat}
  {L U : Finset V}
-- given
  (hBpos : 0 < B)
  (hBp : ∀ {v w : V} (hvw : P.graph.Adj v w) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hvw t - D.primalEmbedding.vertex v) i| ≤ B)
  (hBd : ∀ {v w : W} (hvw : Pdual.graph.Adj v w) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hvw t - D.dualEmbedding.vertex v) i| ≤ B)
  (hrR : rDual < Rcage)
  (hRightWidth : A + 10 * B < Rcage)
  (hBottom : C + 10 * B < Tbottom)
  (hTop : Ttop + 10 * B < D0)
  (hrootRight : rDual + B ≤ A)
  (hrootBottom : Tbottom < c)
  (hrootTop : d < Ttop)
  (hrectBottom : C ≤ c)
  (hrectTop : d ≤ D0)
  (hsubset : D.primalEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent rPrimal Rdeep c d width L U ⊆ threeCrossingCageEvent D B rDual Rcage C D0 A Tbottom Ttop) :
-- imply
  Disjoint (D.primalEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent rPrimal Rdeep c d width L U) ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster rDual c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.finiteDeepOpenExitedJoinedBoundaryArmEvent_disjoint_boundaryBand_of_subset_cage D hBpos hBp hBd hrR hRightWidth hBottom hTop hrootRight hrootBottom hrootTop hrectBottom hrectTop hsubset


-- created on 2026-10-23
