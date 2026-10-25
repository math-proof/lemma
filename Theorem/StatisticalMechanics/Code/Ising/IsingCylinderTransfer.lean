/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingCylinderTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PositiveTransferObservable
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Def.StatisticalMechanics.Code.Ising.IsingCylinderTransfer
open Finset Matrix Filter Topology
open scoped BigOperators


namespace StatMech.Ising

noncomputable section

variable {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]


theorem cylinderInterLayerInteraction_symm
    (Jvertical : W -> Real) (s t : ConfigSpace W) :
    cylinderInterLayerInteraction Jvertical s t =
      cylinderInterLayerInteraction Jvertical t s := by
  unfold cylinderInterLayerInteraction
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem isingCylinderTransfer_isHermitian
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (h Jvertical : W -> Real) :
    (isingCylinderTransfer E J h Jvertical).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro s t
  simp only [isingCylinderTransfer, star_trivial]
  rw [cylinderInterLayerInteraction_symm]
  congr 1
  ring

theorem isingCylinderTransfer_pos
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (h Jvertical : W -> Real)
    (s t : ConfigSpace W) :
    0 < isingCylinderTransfer E J h Jvertical s t := Real.exp_pos _


end
end StatMech.Ising
