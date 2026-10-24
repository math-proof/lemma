import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PottsClusterSumContinuity
open Filter MeasureTheory Set Topology StatMech StatMech.FK


/--
[tendsto_probabilityMeasure_map_of_ae_continuousAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumContinuity.lean)
-/
@[path]
private lemma tendsto_probabilityMeasure_map_of_ae_continuousAt_eq
  [MeasurableSpace Omega]
  [TopologicalSpace Omega]
  [OpensMeasurableSpace Omega]
  [HasOuterApproxClosed Omega]
  [MeasurableSpace Xi]
  [TopologicalSpace Xi]
  [OpensMeasurableSpace Xi]
  {L : Filter I}
  [L.IsCountablyGenerated]
  {mu : ProbabilityMeasure Omega}
-- given
  (muSeq : I -> ProbabilityMeasure Omega)
  (hmu : Tendsto muSeq L (nhds mu))
  (f : Omega -> Xi)
  (hf : Measurable f)
  (hcontinuous : ∀ᵐ x ∂(mu : Measure Omega), ContinuousAt f x) :
-- imply
  Tendsto (fun i => (muSeq i).map hf.aemeasurable) L (nhds (mu.map hf.aemeasurable)) := by
-- proof
  apply StatMech.FK.tendsto_probabilityMeasure_map_of_ae_continuousAt muSeq mu hmu f hf hcontinuous

/--
[cluster_eq_of_mem_finiteClusterEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumContinuity.lean)
-/
@[path]
private lemma cluster_eq_of_mem_finiteClusterEvent_eq
  {d : Nat}
  {omega eta : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hfin : (cluster d omega x).Finite)
  (heta : eta ∈ clusterEvent d (StatMech.FrontierB.finiteClusterNeighborhood omega x hfin : Set (Site d)) x (cluster d omega x)) :
-- imply
  cluster d eta x = cluster d omega x := by
-- proof
  apply StatMech.FK.cluster_eq_of_mem_finiteClusterEvent omega eta x hfin heta

/--
[continuousAt_pottsClusterSumSpin_apply_of_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumContinuity.lean)
-/
@[path]
private lemma continuousAt_pottsClusterSumSpin_apply_of_finite_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {x : Site d}
-- given
  (input : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q))
  (hfin : (cluster d input.1 x).Finite) :
-- imply
  ContinuousAt (fun z => pottsClusterSumSpin boundaryColor z.1 z.2 x) input := by
-- proof
  apply StatMech.FK.continuousAt_pottsClusterSumSpin_apply_of_finite boundaryColor input x hfin

/--
[continuousAt_pottsClusterSumSpin_of_allClustersFinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumContinuity.lean)
-/
@[path]
private lemma continuousAt_pottsClusterSumSpin_of_allClustersFinite_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
-- given
  (input : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q))
  (hfinite : input.1 ∈ pottsAllClustersFiniteEvent d) :
-- imply
  ContinuousAt (fun z => pottsClusterSumSpin boundaryColor z.1 z.2) input := by
-- proof
  apply StatMech.FK.continuousAt_pottsClusterSumSpin_of_allClustersFinite boundaryColor input hfinite

/--
[continuousAt_pottsClusterSumJointFactor_of_allClustersFinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumContinuity.lean)
-/
@[path]
private lemma continuousAt_pottsClusterSumJointFactor_of_allClustersFinite_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
-- given
  (input : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q))
  (hfinite : input.1 ∈ pottsAllClustersFiniteEvent d) :
-- imply
  ContinuousAt (pottsClusterSumJointFactor boundaryColor) input := by
-- proof
  apply StatMech.FK.continuousAt_pottsClusterSumJointFactor_of_allClustersFinite boundaryColor input hfinite

/--
[tendsto_pottsClusterSumJointProbabilityMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumContinuity.lean)
-/
@[path]
private lemma tendsto_pottsClusterSumJointProbabilityMeasure_eq
  {d q : Nat}
  [NeZero q]
  {L : Filter I}
  [L.IsCountablyGenerated]
  {boundaryColor : Fin q}
  {edgeLimit : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
-- given
  (edgeSeq : I -> ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
  (hedge : Tendsto edgeSeq L (nhds edgeLimit))
  (hfinite : ∀ᵐ omega ∂(edgeLimit : Measure _), omega ∈ pottsAllClustersFiniteEvent d) :
-- imply
  Tendsto (fun i => pottsClusterSumJointProbabilityMeasure boundaryColor (edgeSeq i)) L (nhds (pottsClusterSumJointProbabilityMeasure boundaryColor edgeLimit)) := by
-- proof
  apply StatMech.FK.tendsto_pottsClusterSumJointProbabilityMeasure boundaryColor edgeSeq edgeLimit hedge hfinite


-- created on 2026-10-23
