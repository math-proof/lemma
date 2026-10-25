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
import Theorem.StatisticalMechanics.Code.FK.PottsErgodicPhaseFamily
open Filter MeasureTheory Set Topology


namespace StatMech.FK

open Lattice Percolation

noncomputable section

def freePottsClusterSumSpinProbabilityMeasure
    (d q : Nat) [NeZero q] (boundaryColor : Fin q)
    {p : Real} (hp : 0 < p) (hp1 : p < 1) :
    ProbabilityMeasure (PottsConfig d q) :=
  let hqR : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  (pottsClusterSumJointProbabilityMeasure boundaryColor
    (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR))).map
      continuous_fst.measurable.aemeasurable


def wiredPottsClusterSumSpinProbabilityMeasure
    (d q : Nat) [NeZero q] (boundaryColor : Fin q)
    {p : Real} (hp : 0 < p) (hp1 : p < 1) :
    ProbabilityMeasure (PottsConfig d q) :=
  let hqR : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  (pottsClusterSumJointProbabilityMeasure boundaryColor
    (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR))).map
      continuous_fst.measurable.aemeasurable


end
end StatMech.FK
