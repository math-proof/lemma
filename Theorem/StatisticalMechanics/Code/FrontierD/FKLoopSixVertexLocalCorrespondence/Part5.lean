/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKLoopSixVertexLocalCorrespondence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorTransferBridge.Part2
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part5
open Finset Matrix


namespace StatMech.FrontierD

theorem fkOrientedLoopSectorPartitionSum_eq_sixVertexSector
    (T : EvenTorus) (n : Fin (T.width + 1)) (lam : Real) :
    fkOrientedLoopSectorPartitionSum T n lam =
      svTorusSectorArrowPartitionSum T n
        (Real.exp (lam / 2) + Real.exp (-lam / 2)) := by
  rw [fkOrientedLoopSectorPartitionSum, svTorusSectorArrowPartitionSum]
  apply Finset.sum_congr rfl
  intro omega homega
  by_cases hn : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n.val
  · simp only [if_pos hn]
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
        exact sum_fkOrientedLoopLocalWeight_eq_sixVertexLocalWeight
          lam omega v
  · simp [hn]


theorem fkOrientedLoopFixedChargePartitionSum_eq_sectorTrace
    (T : EvenTorus) (r : Nat) (_hr : r <= T.width / 2) (lam : Real) :
    fkOrientedLoopSectorPartitionSum T
        ⟨T.width / 2 - r, Nat.lt_succ_of_le
          ((Nat.sub_le _ _).trans (Nat.div_le_self T.width 2))⟩ lam =
      Matrix.trace
        (sixVertexSectorTransfer T.width (T.width / 2 - r)
          (Real.exp (lam / 2) + Real.exp (-lam / 2)) ^ T.height) := by
  rw [fkOrientedLoopSectorPartitionSum_eq_sixVertexSector]
  exact svTorusSectorArrowPartitionSum_eq_sectorTrace T _ _

end StatMech.FrontierD
