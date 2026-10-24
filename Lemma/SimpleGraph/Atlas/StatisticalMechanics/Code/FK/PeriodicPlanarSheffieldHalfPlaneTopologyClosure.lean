import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneTopologyClosure
open MeasureTheory Set StatMech StatMech.FK StatMech.FK.PeriodicPlanar StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair


/--
[threeCrossingCageEvent_disjoint_boundaryBandHasInfiniteCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneTopologyClosure.lean)
-/
@[path]
private lemma threeCrossingCageEvent_disjoint_boundaryBandHasInfiniteCluster_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {B r R C D0 A Tbottom Ttop c d : Real}
-- given
  (hBpos : 0 < B)
  (hBp : ∀ {u v : V} (huv : P.graph.Adj u v) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc huv t - D.primalEmbedding.vertex u) i| ≤ B)
  (hBd : ∀ {u v : W} (huv : Pdual.graph.Adj u v) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc huv t - D.dualEmbedding.vertex u) i| ≤ B)
  (hrR : r < R)
  (hRightWidth : A + 10 * B < R)
  (hBottom : C + 10 * B < Tbottom)
  (hTop : Ttop + 10 * B < D0)
  (hrootRight : r + B ≤ A)
  (hrootBottom : Tbottom < c)
  (hrootTop : d < Ttop)
  (hrectBottom : C ≤ c)
  (hrectTop : d ≤ D0) :
-- imply
  Disjoint (threeCrossingCageEvent D B r R C D0 A Tbottom Ttop) ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster r c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.threeCrossingCageEvent_disjoint_boundaryBandHasInfiniteCluster D hBpos hBp hBd hrR hRightWidth hBottom hTop hrootRight hrootBottom hrootTop hrectBottom hrectTop

/--
[finiteJoinedBoundaryArmEvent_disjoint_boundaryBand_of_subset_cage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneTopologyClosure.lean)
-/
@[path]
private lemma finiteJoinedBoundaryArmEvent_disjoint_boundaryBand_of_subset_cage_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {B r R C D0 A Tbottom Ttop c d : Real}
  {rPrimal cPrimal dPrimal : Real}
  {n : Nat}
  {L U : Finset V}
-- given
  (hBpos : 0 < B)
  (hBp : ∀ {u v : V} (huv : P.graph.Adj u v) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc huv t - D.primalEmbedding.vertex u) i| ≤ B)
  (hBd : ∀ {u v : W} (huv : Pdual.graph.Adj u v) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc huv t - D.dualEmbedding.vertex u) i| ≤ B)
  (hrR : r < R)
  (hRightWidth : A + 10 * B < R)
  (hBottom : C + 10 * B < Tbottom)
  (hTop : Ttop + 10 * B < D0)
  (hrootRight : r + B ≤ A)
  (hrootBottom : Tbottom < c)
  (hrootTop : d < Ttop)
  (hrectBottom : C ≤ c)
  (hrectTop : d ≤ D0)
  (hjoined : D.primalEmbedding.finiteJoinedBoundaryArmEvent rPrimal cPrimal dPrimal n L U ⊆ threeCrossingCageEvent D B r R C D0 A Tbottom Ttop) :
-- imply
  Disjoint (D.primalEmbedding.finiteJoinedBoundaryArmEvent rPrimal cPrimal dPrimal n L U) ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster r c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.finiteJoinedBoundaryArmEvent_disjoint_boundaryBand_of_subset_cage D hBpos hBp hBd hrR hRightWidth hBottom hTop hrootRight hrootBottom hrootTop hrectBottom hrectTop hjoined


-- created on 2026-10-23
