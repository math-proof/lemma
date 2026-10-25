/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredTranslatedBoundary.Part6
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredTruncationLimit.Part2
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Def.StatisticalMechanics.Code.FK.PottsClusterSumWiredComparison.Part2
open Filter MeasureTheory Set Topology
open scoped BigOperators


namespace StatMech.FK

open Lattice Percolation

noncomputable section

theorem measurableSet_pottsSpinTruncationDisagreement
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) (R : Nat)
    (sites : Finset (Site d)) :
    MeasurableSet (pottsSpinTruncationDisagreement boundaryColor R sites) := by
  apply MeasurableSet.biUnion sites.countable_toSet
  intro x hx
  apply MeasurableSet.compl
  apply measurableSet_eq_fun
  · exact (measurable_pi_apply x).comp
      (measurable_pottsClusterSumSpin_wiredTruncationEdge boundaryColor R)
  · exact measurable_pottsClusterSumSpin_apply boundaryColor x


theorem pottsSpinCylinder_membership_iff_of_not_disagreement
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) (R : Nat)
    (sites : Finset (Site d)) (colors : Set (∀ _x : sites, Fin q))
    (input : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q))
    (hinput : input ∉ pottsSpinTruncationDisagreement boundaryColor R sites) :
    pottsClusterSumSpin boundaryColor input.1 input.2 ∈
        cylinder (α := fun _ : Site d => Fin q) sites colors ↔
      pottsClusterSumSpin boundaryColor
          (wiredTruncationEdge d R input.1) input.2 ∈
        cylinder (α := fun _ : Site d => Fin q) sites colors := by
  rw [mem_cylinder, mem_cylinder]
  have heq : sites.restrict
      (pottsClusterSumSpin boundaryColor input.1 input.2) =
      sites.restrict (pottsClusterSumSpin boundaryColor
        (wiredTruncationEdge d R input.1) input.2) := by
    funext x
    apply not_ne_iff.mp
    intro hne
    apply hinput
    rw [pottsSpinTruncationDisagreement]
    exact Set.mem_iUnion_of_mem x.1
      (Set.mem_iUnion_of_mem x.2 hne.symm)
  rw [heq]


theorem pottsSpinTruncationDisagreement_real_le
    {d q : Nat} [NeZero q] (hd : 2 ≤ d)
    (boundaryColor : Fin q) (R : Nat) (hR : 1 ≤ R)
    (sites : Finset (Site d))
    (hsites : ∀ x ∈ sites, x ∈ box d R)
    (edgeMeasure : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
    ((edgeMeasure : Measure _).prod (pottsIIDLabelMeasure d q)).real
        (pottsSpinTruncationDisagreement boundaryColor R sites) ≤
      ∑ x ∈ sites, (edgeMeasure : Measure _).real
        (wiredTruncationErrorEvent d R x) := by
  let E := fun x : Site d =>
    {input : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) |
      pottsClusterSumSpin boundaryColor
          (wiredTruncationEdge d R input.1) input.2 x ≠
        pottsClusterSumSpin boundaryColor input.1 input.2 x}
  calc
    ((edgeMeasure : Measure _).prod (pottsIIDLabelMeasure d q)).real
        (pottsSpinTruncationDisagreement boundaryColor R sites) ≤
      ∑ x ∈ sites,
        ((edgeMeasure : Measure _).prod (pottsIIDLabelMeasure d q)).real
          (E x) := by
            exact measureReal_biUnion_finset_le sites E
    _ ≤ ∑ x ∈ sites, (edgeMeasure : Measure _).real
        (wiredTruncationErrorEvent d R x) := by
      apply Finset.sum_le_sum
      intro x hx
      have hsub : E x ⊆ Prod.fst ⁻¹' wiredTruncationErrorEvent d R x := by
        intro input hinput
        simpa [wiredTruncationErrorEvent, wiredTruncatedInfiniteEvent,
          clusterInfiniteEvent] using
            (cluster_status_of_pottsClusterSumSpin_wiredTruncationEdge_ne
              hd hR boundaryColor input.1 input.2 x (hsites x hx) hinput)
      have hmono := measureReal_mono (μ :=
        (edgeMeasure : Measure _).prod (pottsIIDLabelMeasure d q)) hsub
      have hpres := (measurePreserving_fst
        (μ := (edgeMeasure : Measure _))
        (ν := pottsIIDLabelMeasure d q)).measureReal_preimage
          (measurableSet_wiredTruncationErrorEvent d R x).nullMeasurableSet
      exact hmono.trans_eq hpres


end
end StatMech.FK
