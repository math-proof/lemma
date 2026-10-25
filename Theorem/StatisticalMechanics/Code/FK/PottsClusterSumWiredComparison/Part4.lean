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
import Def.StatisticalMechanics.Code.FK.PottsClusterSumWiredComparison.Part3
open Filter MeasureTheory Set Topology
open scoped BigOperators


namespace StatMech.FK

open Lattice Percolation

noncomputable section

theorem pottsClusterSumSpinProbabilityMeasure_eq_joint_map_fst
    {d q : Nat} [NeZero q] (boundaryColor : Fin q)
    (edgeMeasure : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
    pottsClusterSumSpinProbabilityMeasure boundaryColor edgeMeasure =
      (pottsClusterSumJointProbabilityMeasure boundaryColor edgeMeasure).map
        continuous_fst.measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  let source : Measure
      (ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) :=
    pottsClusterFactorInputProbabilityMeasure (q := q) edgeMeasure
  calc
    Measure.map (fun input =>
        pottsClusterSumSpin boundaryColor input.1 input.2) source =
      Measure.map (Prod.fst ∘ pottsClusterSumJointFactor boundaryColor)
        source := rfl
    _ = Measure.map Prod.fst
        (Measure.map (pottsClusterSumJointFactor boundaryColor) source) :=
      (Measure.map_map measurable_fst
        (measurable_pottsClusterSumJointFactor boundaryColor)).symm


theorem abs_clusterSumSpin_sub_truncated_real_le
    {d q : Nat} [NeZero q] (hd : 2 ≤ d)
    (boundaryColor : Fin q) (R : Nat) (hR : 1 ≤ R)
    (sites : Finset (Site d)) (colors : Set (∀ _x : sites, Fin q))
    (hsites : ∀ x ∈ sites, x ∈ box d R)
    (edgeMeasure : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
    abs ((pottsClusterSumSpinProbabilityMeasure boundaryColor edgeMeasure : Measure _).real
          (cylinder (α := fun _ : Site d => Fin q) sites colors) -
        (wiredTruncatedPottsClusterSumSpinProbabilityMeasure
          boundaryColor edgeMeasure R : Measure _).real
          (cylinder (α := fun _ : Site d => Fin q) sites colors)) ≤
      ∑ x ∈ sites, (edgeMeasure : Measure _).real
        (wiredTruncationErrorEvent d R x) := by
  let source : Measure
      (ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) :=
    (edgeMeasure : Measure _).prod (pottsIIDLabelMeasure d q)
  let f : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) ->
      PottsConfig d q := fun input =>
    pottsClusterSumSpin boundaryColor input.1 input.2
  let g : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) ->
      PottsConfig d q := fun input =>
    pottsClusterSumSpin boundaryColor
      (wiredTruncationEdge d R input.1) input.2
  let C := cylinder (α := fun _ : Site d => Fin q) sites colors
  let D := pottsSpinTruncationDisagreement boundaryColor R sites
  have hbase := abs_map_real_sub_map_real_le_error source f g
    (measurable_pottsClusterSumSpin boundaryColor)
    (measurable_pottsClusterSumSpin_wiredTruncationEdge boundaryColor R)
    C (isClopen_pottsSpinCylinder sites colors).isOpen.measurableSet D
    (fun input hinput =>
      pottsSpinCylinder_membership_iff_of_not_disagreement
        boundaryColor R sites colors input hinput)
  refine hbase.trans ?_
  exact pottsSpinTruncationDisagreement_real_le
    hd boundaryColor R hR sites hsites edgeMeasure

end
end StatMech.FK
