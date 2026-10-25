/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsErgodicPhaseFamily.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredOrder
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredErgodicity
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumProductErgodicity.Part3
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumContinuity.Part2
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWeakLimitIdentification.Part6
import Theorem.StatisticalMechanics.Code.FK.OrderTransition.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FK

open Lattice Percolation

noncomputable section

theorem pottsClusterSumJointMeasure_otherColor_real
    {d q : Nat} [NeZero q] (boundaryColor a : Fin q)
    (hba : boundaryColor ≠ a)
    (edgeMeasure : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure edgeMeasure] (x : Site d) :
    (Measure.map Prod.fst
        (pottsClusterSumJointMeasure boundaryColor edgeMeasure)).real
        (pottsColorEvent d q x a) =
      (1 / (q : Real)) *
        edgeMeasure.real {omega | (cluster d omega x).Finite} := by
  have h := congrArg ENNReal.toReal
    (pottsClusterSumJointMeasure_otherColor_apply
      boundaryColor a hba edgeMeasure x)
  have htop : edgeMeasure {omega | (cluster d omega x).Finite} ≠ ⊤ :=
    measure_ne_top edgeMeasure _
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv] at h
  simpa only [Measure.real, ENNReal.toReal_natCast, one_div] using h


end
end StatMech.FK
