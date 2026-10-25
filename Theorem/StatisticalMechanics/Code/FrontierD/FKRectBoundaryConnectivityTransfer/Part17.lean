/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.Foundations.FiniteNonnegativeMatrixRate.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part19
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


@[simp] theorem fkRectBoundaryNonSeamRow_val (R : FKRectTorus)
    (i : Fin (R.height - 1)) :
    (fkRectBoundaryNonSeamRow R i).val = i.val + 1 := rfl


theorem fkRect_sum_rows_eq_seam_add_nonSeam
    (R : FKRectTorus) (f : Fin R.height -> Nat) :
    (∑ y, f y) = f (fkRectBoundarySeamRow R) +
      ∑ i : Fin (R.height - 1), f (fkRectBoundaryNonSeamRow R i) := by
  let e : Fin (R.height - 1 + 1) ≃ Fin R.height :=
    finCongr (Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr R.height_pos.ne'))
  rw [← Equiv.sum_comp e f, Fin.sum_univ_succ]
  rfl


end
end StatMech.FrontierD
