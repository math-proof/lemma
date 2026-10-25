/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKLoopSixVertexLocalCorrespondence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorTransferBridge.Part2
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part3
open Finset Matrix


namespace StatMech.FrontierD

theorem fkOrientedLoopPartitionSum_eq_sixVertexTorusArrowPartitionSum
    (T : EvenTorus) (lam : Real) :
    fkOrientedLoopPartitionSum T lam =
      sixVertexTorusArrowPartitionSum T
        (Real.exp (lam / 2) + Real.exp (-lam / 2)) := by
  rw [fkOrientedLoopPartitionSum, sixVertexTorusArrowPartitionSum]
  apply Finset.sum_congr rfl
  intro omega homega
  change (∑ pairing : FKMedialLoopPairing T,
      ∏ v, fkOrientedLoopLocalWeight lam (pairing v) omega v) =
    ∏ v, omega.localWeight
      (Real.exp (lam / 2) + Real.exp (-lam / 2)) v
  calc
    (∑ pairing : FKMedialLoopPairing T,
        ∏ v, fkOrientedLoopLocalWeight lam (pairing v) omega v) =
      ∏ v, ∑ pairing : Bool,
        fkOrientedLoopLocalWeight lam pairing omega v :=
      (Fintype.prod_sum (fun v pairing =>
        fkOrientedLoopLocalWeight lam pairing omega v)).symm
    _ = ∏ v, omega.localWeight
        (Real.exp (lam / 2) + Real.exp (-lam / 2)) v := by
      apply Finset.prod_congr rfl
      intro v hv
      exact sum_fkOrientedLoopLocalWeight_eq_sixVertexLocalWeight lam omega v


end StatMech.FrontierD
