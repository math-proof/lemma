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
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part40
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


theorem fkRectBoundaryConnectivityLayerTransfer_nonneg
    {W : Nat} (hW : 0 < W) {q : Real} (hq : 0 < q)
    (evenRow : Bool) (source target : FKRectBoundaryConnectivityState W) :
    0 <= fkRectBoundaryConnectivityLayerTransfer hW q evenRow source target := by
  unfold fkRectBoundaryConnectivityLayerTransfer
  exact Finset.sum_nonneg fun eta _ => by
    split_ifs
    · exact (fkRectBoundaryLayerWeight_pos hW hq evenRow source.1 eta).le
    · exact le_rfl


theorem fkRectBoundaryConnectivityLayerTransfer_diag_pos
    {W : Nat} (hW : 0 < W) {q : Real} (hq : 0 < q)
    (evenRow : Bool) (state : FKRectBoundaryConnectivityState W) :
    0 < fkRectBoundaryConnectivityLayerTransfer hW q evenRow state state := by
  let vertical : Bool × Fin W -> Bool := fkRectBoundaryVerticalLayer
  have houtput : fkRectBoundaryConnectivityLayerOutput hW evenRow state vertical =
      state := by
    apply Subtype.ext
    exact fkRectBoundaryLayerOutput_vertical hW evenRow state.1 state.2
  have hterm : 0 <
      (if fkRectBoundaryConnectivityLayerOutput hW evenRow state vertical = state
        then fkRectBoundaryLayerWeight hW q evenRow state.1 vertical else 0) := by
    rw [if_pos houtput]
    exact fkRectBoundaryLayerWeight_pos hW hq evenRow state.1 vertical
  apply lt_of_lt_of_le hterm
  unfold fkRectBoundaryConnectivityLayerTransfer
  have hle := Finset.single_le_sum
    (s := Finset.univ)
    (f := fun eta : Bool × Fin W -> Bool =>
      if fkRectBoundaryConnectivityLayerOutput hW evenRow state eta = state then
        fkRectBoundaryLayerWeight hW q evenRow state.1 eta else 0)
    (fun eta _ => by
      dsimp only
      split_ifs
      · exact (fkRectBoundaryLayerWeight_pos hW hq evenRow state.1 eta).le
      · exact le_rfl)
    (Finset.mem_univ vertical)
  simpa using hle


end
end StatMech.FrontierD
