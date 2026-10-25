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
open Filter Function MeasureTheory MeasurableSpace Set Topology
open scoped ENNReal symmDiff


namespace StatMech.FK

def MixingAgainst {Beta : Type*} [MeasurableSpace Beta]
    (S : Beta -> Beta) (nu : Measure Beta) (D : Set (Set Beta)) : Prop :=
  forall (A : Set Beta), MeasurableSet A -> forall B, B ∈ D ->
    Tendsto (fun n : Nat =>
      nu.real (A ∩ (S^[n]) ⁻¹' B)) atTop
      (nhds (nu.real A * nu.real B))

end StatMech.FK
