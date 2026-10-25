import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4WiredPhaseInput.Part2
open MeasureTheory Set SimpleGraph StatMech StatMech.FrontierD


/--
[measurableSet_originIsolatedCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4WiredPhaseInput.lean)
-/
@[path]
private lemma measurableSet_originIsolatedCylinder_eq
  {d : Nat} :
-- imply
  MeasurableSet (originIsolatedCylinder d) := by
-- proof
  apply StatMech.FrontierD.measurableSet_originIsolatedCylinder d

/--
[setPattern_mem_originIsolatedCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4WiredPhaseInput.lean)
-/
@[path]
private lemma setPattern_mem_originIsolatedCylinder_eq
  {d : Nat}
  {omega : ConfigSpace (Sym2 (Site d))} :
-- imply
  FK.setPattern (originIncidentEdges d) (originIncidentClosedPattern d) omega ∈ originIsolatedCylinder d := by
-- proof
  apply StatMech.FrontierD.setPattern_mem_originIsolatedCylinder d omega

/--
[cluster_origin_eq_singleton_of_mem_originIsolatedCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4WiredPhaseInput.lean)
-/
@[path]
private lemma cluster_origin_eq_singleton_of_mem_originIsolatedCylinder_eq
  {d : Nat}
  {omega : ConfigSpace (Sym2 (Site d))}
-- given
  (homega : omega ∈ originIsolatedCylinder d) :
-- imply
  cluster d omega (origin d) = {origin d} := by
-- proof
  apply StatMech.FrontierD.cluster_origin_eq_singleton_of_mem_originIsolatedCylinder homega

/--
[originIsolatedCylinder_subset_percolationEvent_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4WiredPhaseInput.lean)
-/
@[path]
private lemma originIsolatedCylinder_subset_percolationEvent_compl_eq
  {d : Nat} :
-- imply
  originIsolatedCylinder d ⊆ (percolationEvent d)ᶜ := by
-- proof
  apply StatMech.FrontierD.originIsolatedCylinder_subset_percolationEvent_compl d

/--
[wiredInfiniteVolume_originIsolatedCylinder_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4WiredPhaseInput.lean)
-/
@[path]
private lemma wiredInfiniteVolume_originIsolatedCylinder_pos_eq
  {d : Nat}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  0 < ((FK.wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure (ConfigSpace (Sym2 (Site d)))) (originIsolatedCylinder d) := by
-- proof
  apply StatMech.FrontierD.wiredInfiniteVolume_originIsolatedCylinder_pos hp hp1 hq

/--
[wiredInfiniteVolume_percolationEvent_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4WiredPhaseInput.lean)
-/
@[path]
private lemma wiredInfiniteVolume_percolationEvent_ne_one_eq
  {d : Nat}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  ((FK.wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure (ConfigSpace (Sym2 (Site d)))) (percolationEvent d) ≠ 1 := by
-- proof
  apply StatMech.FrontierD.wiredInfiniteVolume_percolationEvent_ne_one hp hp1 hq

/--
[measurableSet_hasInfiniteClusterEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4WiredPhaseInput.lean)
-/
@[path]
private lemma measurableSet_hasInfiniteClusterEvent_eq
  {d : Nat} :
-- imply
  MeasurableSet (hasInfiniteClusterEvent d) := by
-- proof
  apply StatMech.FrontierD.measurableSet_hasInfiniteClusterEvent d

/--
[percolationProbability_pos_of_hasInfiniteCluster_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4WiredPhaseInput.lean)
-/
@[path]
private lemma percolationProbability_pos_of_hasInfiniteCluster_ae_eq
  {d : Nat}
  {mu : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure mu]
-- given
  (hTI : ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) mu)
  (hglobal : mu (hasInfiniteClusterEvent d) = 1) :
-- imply
  0 < mu.real (percolationEvent d) := by
-- proof
  apply StatMech.FrontierD.percolationProbability_pos_of_hasInfiniteCluster_ae mu hTI hglobal

/--
[wiredInfiniteVolume_percolationEvent_pos_of_hasInfiniteCluster_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4WiredPhaseInput.lean)
-/
@[path]
private lemma wiredInfiniteVolume_percolationEvent_pos_of_hasInfiniteCluster_ae_eq
  {d : Nat}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hglobal : ((FK.wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure (ConfigSpace (Sym2 (Site d)))) (hasInfiniteClusterEvent d) = 1) :
-- imply
  0 < ((FK.wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure (ConfigSpace (Sym2 (Site d)))).real (percolationEvent d) := by
-- proof
  apply StatMech.FrontierD.wiredInfiniteVolume_percolationEvent_pos_of_hasInfiniteCluster_ae hp hp1 hq hglobal

/--
[fkQgt4_discontinuity_of_winding_and_positive_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4WiredPhaseInput.lean)
-/
@[path]
private lemma fkQgt4_discontinuity_of_winding_and_positive_order_eq
  {q xiInv : Real}
-- given
  (hq : 4 < q)
  (hxi : 0 < xiInv)
  (hrate : Filter.Tendsto (fkQgt4CriticalFreeDiagonalRate hq) Filter.atTop (nhds xiInv))
  (hWiredPositive : let mu := ((FK.wiredInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) 0 < mu.real (percolationEvent 2))
  (hwind : FKQgt4TorusSixVertexWindingBridge xiInv (fkQgt4SixVertexGapRate q)) :
-- imply
  FK.IsFirstOrderTransition 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) ∧ FK.freeInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) ≠ FK.wiredInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) ∧ Filter.Tendsto (fkQgt4CriticalFreeDiagonalRate hq) Filter.atTop (nhds (fkQgt4SixVertexGapRate q)) ∧ 0 < fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_discontinuity_of_winding_and_positive_order hq hxi hrate hWiredPositive hwind

/--
[fkQgt4_discontinuity_of_winding_and_global_wired_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4WiredPhaseInput.lean)
-/
@[path]
private lemma fkQgt4_discontinuity_of_winding_and_global_wired_order_eq
  {q xiInv : Real}
-- given
  (hq : 4 < q)
  (hxi : 0 < xiInv)
  (hrate : Filter.Tendsto (fkQgt4CriticalFreeDiagonalRate hq) Filter.atTop (nhds xiInv))
  (hglobal : ((FK.wiredInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) (hasInfiniteClusterEvent 2) = 1)
  (hwind : FKQgt4TorusSixVertexWindingBridge xiInv (fkQgt4SixVertexGapRate q)) :
-- imply
  FK.IsFirstOrderTransition 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) ∧ FK.freeInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) ≠ FK.wiredInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) ∧ Filter.Tendsto (fkQgt4CriticalFreeDiagonalRate hq) Filter.atTop (nhds (fkQgt4SixVertexGapRate q)) ∧ 0 < fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_discontinuity_of_winding_and_global_wired_order hq hxi hrate hglobal hwind


-- created on 2026-10-23
