/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Def.StatisticalMechanics.Code.FK.PottsClusterSumFactor.Part10
open MeasureTheory Set


namespace StatMech.FK

open Lattice Percolation


theorem pottsClusterSumJointMeasure_isProbabilityMeasure
    {d q : Nat} [NeZero q] (boundaryColor : Fin q)
    (edgeMeasure : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure edgeMeasure] :
    IsProbabilityMeasure
      (pottsClusterSumJointMeasure boundaryColor edgeMeasure) := by
  unfold pottsClusterSumJointMeasure
  exact inferInstance


theorem pottsClusterSumJointMeasure_map_snd
    {d q : Nat} [NeZero q] (boundaryColor : Fin q)
    (edgeMeasure : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure edgeMeasure] :
    Measure.map Prod.snd
        (pottsClusterSumJointMeasure boundaryColor edgeMeasure) =
      edgeMeasure := by
  rw [pottsClusterSumJointMeasure,
    Measure.map_map measurable_snd
      (measurable_pottsClusterSumJointFactor boundaryColor)]
  change Measure.map Prod.fst
      (edgeMeasure.prod (pottsIIDLabelMeasure d q)) = edgeMeasure
  exact measurePreserving_fst.map_eq

end StatMech.FK
