/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumProductErgodicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumErgodicFactor.Part2
import Theorem.StatisticalMechanics.Code.FK.FreePairMixingFromTail.Part3
import Theorem.StatisticalMechanics.Code.FK.FreeTailTriviality
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
import Def.StatisticalMechanics.Code.FK.PottsClusterSumProductErgodicity.Part3
open Filter Function MeasureTheory MeasurableSpace Set Topology
open scoped ENNReal symmDiff


namespace StatMech.FK

open Lattice

theorem measurableSet_pottsAllClustersFiniteEvent (d : Nat) :
    MeasurableSet (pottsAllClustersFiniteEvent d) := by
  exact MeasurableSet.iInter fun x =>
    (Percolation.measurableSet_clusterInfinite x).compl

theorem mem_pottsAllClustersFiniteEvent_iff {d : Nat}
    (omega : ConfigSpace (Sym2 (Site d))) :
    omega ∈ pottsAllClustersFiniteEvent d ↔
      forall x : Site d, (cluster d omega x).Finite := by
  simp only [pottsAllClustersFiniteEvent, Set.mem_iInter, Set.mem_compl_iff,
    Set.mem_setOf_eq]
  exact forall_congr' fun _ => not_infinite


theorem ae_pottsAllClustersFinite_of_translationInvariant_of_origin_zero
    {d : Nat} (edgeMeasure : Measure (ConfigSpace (Sym2 (Site d))))
    (htrans : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site d)) edgeMeasure)
    (horigin : edgeMeasure
      {omega : ConfigSpace (Sym2 (Site d)) |
        (cluster d omega (Percolation.origin d)).Infinite} = 0) :
    ∀ᵐ omega ∂edgeMeasure, omega ∈ pottsAllClustersFiniteEvent d := by
  have hsite : forall x : Site d,
      edgeMeasure
        {omega : ConfigSpace (Sym2 (Site d)) |
          (cluster d omega x).Infinite} = 0 := by
    intro x
    let g : Multiplicative (Site d) := Multiplicative.ofAdd x
    have hgx : g • Percolation.origin d = x := by
      show Multiplicative.toAdd g + (0 : Site d) = x
      simp [g]
    have hpre :
        (ConfigSpace.shift g : ConfigSpace (Sym2 (Site d)) ->
          ConfigSpace (Sym2 (Site d))) ⁻¹'
            {omega | (cluster d omega x).Infinite} =
          {omega | (cluster d omega (Percolation.origin d)).Infinite} := by
      ext omega
      change (cluster d (ConfigSpace.shift g omega) x).Infinite <->
        (cluster d omega (Percolation.origin d)).Infinite
      rw [← hgx, Percolation.cluster_shift]
      exact Set.infinite_image_iff
        (Set.injOn_of_injective fun _ _ h => smul_left_cancel g h)
    have hinv := htrans.measure_preimage g
      (Percolation.measurableSet_clusterInfinite x)
    rw [hpre] at hinv
    exact hinv.symm.trans horigin
  rw [ae_iff]
  change edgeMeasure (pottsAllClustersFiniteEvent d)ᶜ = 0
  rw [pottsAllClustersFiniteEvent, compl_iInter]
  simp only [compl_compl]
  exact measure_iUnion_null hsite


theorem pottsClusterSumJointFactor_eq_of_allClustersFinite
    {d q : Nat} [NeZero q] (a b : Fin q)
    (input : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q))
    (hfinite : input.1 ∈ pottsAllClustersFiniteEvent d) :
    pottsClusterSumJointFactor a input =
      pottsClusterSumJointFactor b input := by
  apply Prod.ext
  · funext x
    simp only [pottsClusterSumJointFactor]
    unfold pottsClusterSumSpin
    rw [
      dif_pos ((mem_pottsAllClustersFiniteEvent_iff input.1).mp hfinite x),
      dif_pos ((mem_pottsAllClustersFiniteEvent_iff input.1).mp hfinite x)]
  · rfl


theorem pottsClusterSumJointMeasure_eq_of_ae_allClustersFinite
    {d q : Nat} [NeZero q] (a b : Fin q)
    (edgeMeasure : Measure (ConfigSpace (Sym2 (Site d))))
    (hfinite : ∀ᵐ omega ∂edgeMeasure,
      omega ∈ pottsAllClustersFiniteEvent d) :
    pottsClusterSumJointMeasure a edgeMeasure =
      pottsClusterSumJointMeasure b edgeMeasure := by
  rw [pottsClusterSumJointMeasure, pottsClusterSumJointMeasure]
  apply Measure.map_congr
  have hprod : ∀ᵐ input ∂edgeMeasure.prod (pottsIIDLabelMeasure d q),
      input.1 ∈ pottsAllClustersFiniteEvent d := by
    rw [Measure.ae_prod_iff_ae_ae]
    · filter_upwards [hfinite] with omega homega
      exact Filter.Eventually.of_forall fun _ => homega
    · exact (measurableSet_pottsAllClustersFiniteEvent d).preimage measurable_fst
  filter_upwards [hprod] with input hinput
  exact pottsClusterSumJointFactor_eq_of_allClustersFinite a b input hinput

end StatMech.FK
