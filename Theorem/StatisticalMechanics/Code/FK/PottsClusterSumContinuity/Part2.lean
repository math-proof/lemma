/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumContinuity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumProductErgodicity.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.FreeInfiniteParityTopology.Part4
import Def.StatisticalMechanics.Code.FK.PottsClusterSumContinuity
open Filter MeasureTheory Set Topology


namespace StatMech.FK

open Lattice Percolation


theorem tendsto_pottsClusterSumJointProbabilityMeasure
    {d q : Nat} [NeZero q] {I : Type*} {L : Filter I}
    [L.IsCountablyGenerated]
    (boundaryColor : Fin q)
    (edgeSeq : I -> ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (edgeLimit : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (hedge : Tendsto edgeSeq L (nhds edgeLimit))
    (hfinite : ∀ᵐ omega ∂(edgeLimit : Measure _),
      omega ∈ pottsAllClustersFiniteEvent d) :
    Tendsto (fun i =>
        pottsClusterSumJointProbabilityMeasure boundaryColor (edgeSeq i))
      L (nhds (pottsClusterSumJointProbabilityMeasure boundaryColor edgeLimit)) := by
  let labelMeasure := pottsIIDLabelProbabilityMeasure d q
  have hpairs : Tendsto (fun i => (edgeSeq i, labelMeasure)) L
      (nhds (edgeLimit, labelMeasure)) :=
    by
      rw [nhds_prod_eq]
      exact hedge.prodMk tendsto_const_nhds
  have hsource : Tendsto (fun i =>
      pottsClusterFactorInputProbabilityMeasure (q := q) (edgeSeq i)) L
      (nhds (pottsClusterFactorInputProbabilityMeasure (q := q) edgeLimit)) := by
    exact ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp hpairs
  have hprodFinite : ∀ᵐ input :
      ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) ∂
      ((pottsClusterFactorInputProbabilityMeasure (q := q) edgeLimit :
        ProbabilityMeasure _) : Measure _),
      input.1 ∈ pottsAllClustersFiniteEvent d := by
    change ∀ᵐ input ∂(edgeLimit : Measure _).prod
      (pottsIIDLabelMeasure d q),
      input.1 ∈ pottsAllClustersFiniteEvent d
    rw [Measure.ae_prod_iff_ae_ae]
    · filter_upwards [hfinite] with omega homega
      exact Filter.Eventually.of_forall fun _ => homega
    · exact (measurableSet_pottsAllClustersFiniteEvent d).preimage measurable_fst
  apply tendsto_probabilityMeasure_map_of_ae_continuousAt
    (fun i => pottsClusterFactorInputProbabilityMeasure (q := q) (edgeSeq i))
    (pottsClusterFactorInputProbabilityMeasure (q := q) edgeLimit)
    hsource (pottsClusterSumJointFactor boundaryColor)
    (measurable_pottsClusterSumJointFactor boundaryColor)
  filter_upwards [hprodFinite] with input hinput
  exact continuousAt_pottsClusterSumJointFactor_of_allClustersFinite
    boundaryColor input hinput

end StatMech.FK
